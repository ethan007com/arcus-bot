#!/usr/bin/env python3
"""Arcus BTC single-file bot (Python >=3.11).

Run: python3 Arcus.py | --once | --check | --self-test
Install: python3 -m pip install -r requirements.txt
Credentials: config.json wallet_address / api_signing_key; blank fields fall back
to ARCUS_WALLET_ADDRESS / ARCUS_SIGNING_KEY environment variables.
No wallet private key is required. No local Python imports.

Official contract checked 2026-10-02:
https://docs.arcus.xyz/api-reference/authentication
https://docs.arcus.xyz/api-reference/exchange/place-order
https://docs.arcus.xyz/api-reference/exchange/cancel-order
https://docs.arcus.xyz/api-reference/public/get-order-status
https://docs.arcus.xyz/api-reference/public/get-account
https://docs.arcus.xyz/api-reference/account/orders

NEED_CONFIRMATION: entry_limit_offset_pct has no inherited value.
NEED_CONFIRMATION: old dynamic 5m grid vs requested fixed grid; select grid_mode.
NEED_CONFIRMATION: old layered/trailing exits vs resting fixed TP; select tp_mode.
NEED_CONFIRMATION: account position units must pass dimensional validation against
live positionValueNotional; never infer scaling from documentation sample numbers.
Runtime JSON + lock are generated, not Python dependencies. Do not delete them.
"""
from __future__ import annotations

# ============================================================
# M1 状态模块
# ============================================================
import argparse
import copy
import fcntl
import hashlib
import json
import math
import os
import queue
import re
import sys
import tempfile
import threading
import time
import uuid
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_DOWN, ROUND_UP
from pathlib import Path
from typing import Any, List, Optional
from urllib.parse import quote

import requests
import certifi
import websocket
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat


ROOT = Path(__file__).resolve().parent
STATES = {'WAIT', 'LONG_WATCH', 'SHORT_WATCH', 'LONG_SIGNAL', 'SHORT_SIGNAL',
          'LONG_ORDER_PENDING', 'SHORT_ORDER_PENDING', 'GRID_LONG', 'GRID_SHORT', 'EXITING'}
TERMINAL = {'FILLED', 'CANCELED', 'MARGIN_CANCELED', 'REJECTED', 'TPSL_CANCELED'}


class SafetyError(RuntimeError):
    pass

def dec(value):
    try:
        x = Decimal(str(value))
    except (InvalidOperation, ValueError, TypeError):
        raise SafetyError('数值无效') from None
    if not x.is_finite():
        raise SafetyError('非有限数值')
    return x

def text_decimal(value):
    return format(dec(value), 'f')

def floor_step(value, step):
    if dec(step) <= 0 or dec(value) < 0:
        raise SafetyError('数量/步长无效')
    return (dec(value)/dec(step)).to_integral_value(rounding=ROUND_DOWN)*dec(step)

def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=path.name+'.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(value, f, ensure_ascii=False, indent=2, allow_nan=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

def load_config(path):
    try:
        cfg = json.loads(Path(path).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        raise SafetyError('config.json 缺失或格式错误，不回退为默认交易配置') from None
    validate_config(cfg)
    required = ('symbol', 'leverage', 'entry_limit_offset_pct', 'first_order_size',
                'size_unit', 'grid_spacing', 'grid_max_layers', 'grid_order_sizes',
                'grid_mode', 'tp_mode', 'take_profit_pct', 'scan_interval_sec', 'dry_run',
                'network', 'account_index', 'wallet_address_env', 'signing_key_env',
                'runtime_dir', 'bot_prefix', 'request_timeout_sec', 'read_retries',
                'retry_backoff_sec', 'history_page_size', 'history_max_pages',
                'candle_count', 'good_til_days', 'entry_timeout_sec', 'cancel_retry_sec',
                'quote_max_age_seconds', 'max_clock_rtt_sec', 'clock_refresh_sec',
                'ws_ping_sec', 'ws_ping_timeout_sec', 'ws_stale_sec', 'ws_reconnect_sec',
                'ws_start_timeout_sec', 'stop_loss_pct', 'cooldown_seconds',
                'take_profit_by_layer', 'trailing_drawdown_by_layer', 'min_profit_usd',
                'fee_buffer_bps', 'add_cooldown_seconds', 'legacy_volatility_bars',
                'legacy_volatility_base', 'legacy_gap_multiplier_min', 'legacy_gap_multiplier_max',
                'max_daily_loss_usd', 'max_daily_drawdown_pct', 'max_margin_equity_pct',
                'max_symbol_equity_pct', 'max_account_equity_pct', 'min_free_collateral_usd',
                'max_spread_bps', 'max_slippage_bps', 'max_signal_price_deviation_pct')
    missing = [k for k in required if k not in cfg]
    if missing:
        raise SafetyError('缺少配置：'+','.join(missing))
    if cfg['symbol'] != 'BTC-USD' or cfg['network'] not in ('mainnet', 'testnet'):
        raise SafetyError('仅支持 Arcus BTC-USD 和 mainnet/testnet')
    if type(cfg['dry_run']) is not bool or type(cfg['account_index']) is not int or not 0 <= cfg['account_index'] <= 9:
        raise SafetyError('dry_run/account_index 无效')
    if cfg['size_unit'] not in ('equity_fraction', 'usd_notional', 'base_qty'):
        raise SafetyError('size_unit 无效')
    if cfg['grid_mode'] not in (None, 'legacy_dynamic', 'fixed') or cfg['tp_mode'] not in (None, 'legacy_layered', 'fixed_limit'):
        raise SafetyError('grid_mode/tp_mode 无效')
    if cfg['tp_mode']=='fixed_limit':
        tiers=cfg.get('take_profit_pct_by_grid_layer')
        if (not isinstance(tiers,list) or len(tiers)!=6
            or any(not 0 < dec(x) < 1 for x in tiers)):
            raise SafetyError('take_profit_pct_by_grid_layer 必须覆盖G0至G5，且每项大于0小于1')
    for k in ('entry_limit_offset_pct', 'take_profit_pct'):
        if cfg[k] is not None and not 0 < dec(cfg[k]) < 1:
            raise SafetyError(k+' 必须为0到1之间的小数，未确认时填null')
    for k in ('first_order_size', 'request_timeout_sec', 'scan_interval_sec', 'retry_backoff_sec',
              'entry_timeout_sec', 'cancel_retry_sec', 'quote_max_age_seconds', 'max_clock_rtt_sec',
              'clock_refresh_sec', 'ws_ping_sec', 'ws_ping_timeout_sec', 'ws_stale_sec',
              'ws_reconnect_sec', 'ws_start_timeout_sec', 'cooldown_seconds', 'add_cooldown_seconds',
              'legacy_volatility_base', 'legacy_gap_multiplier_min', 'legacy_gap_multiplier_max',
              'max_daily_loss_usd', 'min_free_collateral_usd', 'max_spread_bps', 'max_slippage_bps'):
        if dec(cfg[k]) <= 0:
            raise SafetyError(k+' 必须大于0')
    for k in ('grid_spacing', 'stop_loss_pct', 'max_daily_drawdown_pct', 'max_margin_equity_pct',
              'max_signal_price_deviation_pct'):
        if not 0 < dec(cfg[k]) < 1:
            raise SafetyError(k+' 必须大于0且小于1')
    # These two limits are NOT margin percentages: they are notional/equity
    # multiples and can legitimately exceed 1 on a leveraged account.
    if not 0 < dec(cfg['max_symbol_equity_pct']) <= dec(cfg['max_account_equity_pct']):
        raise SafetyError('单币名义金额上限必须大于0，且不超过账户名义金额上限')
    for k, low, high in [('leverage',1,1000), ('grid_max_layers',0,5), ('read_retries',1,10),
                         ('history_page_size',2,1000), ('history_max_pages',1,1000),
                         ('candle_count',130,1500), ('good_til_days',32,365), ('legacy_volatility_bars',2,120)]:
        if type(cfg[k]) is not int or not low <= cfg[k] <= high:
            raise SafetyError(k+' 超出范围')
    if (not isinstance(cfg['grid_order_sizes'],list) or len(cfg['grid_order_sizes']) != cfg['grid_max_layers']
        or any(dec(x) <= 0 for x in cfg['grid_order_sizes'])):
        raise SafetyError('grid_order_sizes 必须逐层覆盖补仓次数（不含首仓）')
    if cfg['grid_mode']=='fixed':
        spacings=cfg.get('grid_spacings')
        if (not isinstance(spacings,list) or len(spacings)!=cfg['grid_max_layers']
            or any(not 0 < dec(x) < 1 for x in spacings)):
            raise SafetyError('grid_spacings 必须逐层覆盖补仓次数，且每项大于0小于1')
    if cfg['size_unit'] == 'equity_fraction' and any(
            dec(x)>dec(cfg['max_symbol_equity_pct'])
            for x in [cfg['first_order_size'],*cfg['grid_order_sizes']]):
        raise SafetyError('单次订单名义金额倍数不能超过单币名义金额上限 max_symbol_equity_pct')
    for k in ('take_profit_by_layer','trailing_drawdown_by_layer'):
        if ((cfg['tp_mode']=='legacy_layered' and len(cfg[k]) < cfg['grid_max_layers']+1)
            or any(not 0 <= dec(x) < 1 for x in cfg[k])):
            raise SafetyError(k+' 必须覆盖首仓与补仓层')
    if any(dec(t)<=0 or dec(d)>=dec(t) for t,d in zip(cfg['take_profit_by_layer'],cfg['trailing_drawdown_by_layer'])):
        raise SafetyError('止盈阈值与回撤配置不一致')
    if cfg['ws_ping_sec'] <= cfg['ws_ping_timeout_sec']:
        raise SafetyError('WS ping间隔必须大于超时')
    if not re.fullmatch(r'[a-z0-9]{1,6}',cfg['bot_prefix']):
        raise SafetyError('bot_prefix 只能为1至6位小写字母或数字')
    for k in ('wallet_address_env','signing_key_env'):
        if not re.fullmatch(r'[A-Z][A-Z0-9_]+',cfg[k]):
            raise SafetyError(k+' 不是合法环境变量名')
    for k in ('wallet_address','api_signing_key'):
        if not isinstance(cfg.get(k,''),str):
            raise SafetyError(k+' 必须为字符串；暂不填写时使用空字符串')
    for k in ('fee_buffer_bps','min_profit_usd'):
        if dec(cfg[k])<0:
            raise SafetyError(k+' 不能小于0')
    return cfg

def credential_value(cfg, field, env_field):
    """Explicit config values take precedence; never log credential values."""
    value=cfg.get(field,'')
    if not isinstance(value,str):
        raise SafetyError(field+' 必须为字符串')
    return value.strip() or os.environ.get(cfg[env_field],'').strip()

def validate_config(cfg):
    if type(cfg.get('hedge_enabled',False)) is not bool or type(cfg.get('grid_enabled',True)) is not bool:
        raise ValueError('hedge_enabled/grid_enabled必须为布尔值')
    if cfg.get('hedge_enabled'):
        interval=cfg.get('hedge_scan_interval_sec',5)
        if type(interval) not in (int,float) or not math.isfinite(interval) or interval<=0:
            raise ValueError('hedge_scan_interval_sec必须为正数')
        if type(cfg.get('hedge_leverage')) is not int or not 1<=cfg['hedge_leverage']<=1000:
            raise ValueError('hedge_leverage必须是1至1000的整数')
        expected={'symbol':'BTC-USD','hedge_symbol':'ETH-USD','grid_enabled':False,
                  'rsi_period':12,'rsi_long_threshold':45,'rsi_short_threshold':55,
                  'first_order_size':5.0,'size_unit':'equity_fraction','take_profit_pct':0.008,
                  'entry_limit_offset_pct':0.0005,'entry_timeout_sec':300}
        if any(cfg.get(k)!=v for k,v in expected.items()):
            raise ValueError('双币种配置与已确认策略不一致')
    for key in ('ema_fast_period', 'ema_slow_period', 'adx_period', 'rsi_period'):
        if type(cfg.get(key)) is not int or not 2 <= cfg[key] <= 120:
            raise ValueError(key + ' 必须为 2 至 120 的整数')
    if cfg['ema_fast_period'] >= cfg['ema_slow_period']:
        raise ValueError('快EMA周期必须小于慢EMA周期')
    for key in ('adx_min', 'rsi_trigger'):
        if type(cfg.get(key)) not in (float, int) or not 0 < cfg[key] < 100:
            raise ValueError(key + ' 必须在 0 和 100 之间')
    for key,default in (('rsi_long_threshold',30),('rsi_short_threshold',70)):
        value=cfg.get(key,default)
        if type(value) not in (float,int) or not 0 < value < 100:
            raise ValueError(key+' 必须在0和100之间')
    if cfg.get('rsi_long_threshold',30)>=cfg.get('rsi_short_threshold',70):
        raise ValueError('LONG RSI阈值必须小于SHORT RSI阈值')
    if cfg.get('entry_timeframe') != '5m':
        raise ValueError('当前策略仅支持 5m RSI 入场')

    # Portfolio-level controls for BTC/ETH paired mode.
    for key in ('pair_take_profit_pct', 'pair_stop_loss_pct'):
        if key in cfg and (not isinstance(cfg[key], (int, float)) or not math.isfinite(cfg[key])
                           or not 0 < cfg[key] < 1):
            raise ValueError(key + ' 必须在0和1之间')
    if 'pair_max_hold_seconds' in cfg:
        value=cfg['pair_max_hold_seconds']
        if type(value) is not int or value < 0:
            raise ValueError('pair_max_hold_seconds 必须是非负整数，0表示不启用')

def log(kind, **fields):
    print('['+kind+'] '+json.dumps(fields, ensure_ascii=False, default=str), flush=True)

def terminal_trade_log(kind, **fields):
    """Console only. A broken output stream must not change order execution."""
    try:
        log(kind, 时间=datetime.now().astimezone().strftime('%Y-%m-%d %H:%M:%S'), **fields)
    except Exception:
        pass


def log_confirmed_trade_events(bot, before):
    """Observe successful persisted reconciliation; never interpret an ACK as a fill."""
    try:
        if not bot.terminal_ready:
            return  # Recovery history is not a new fill event.
        pos=bot.position()
        for cid,rec in bot.state['orders'].items():
            old=before['orders'].get(cid)
            if old is None:
                continue
            if rec['role']=='G' and dec(rec['filled'])>dec(old['filled']):
                complete=dec(rec['filled'])==dec(rec['body']['quantity']) and rec['terminal']
                terminal_trade_log('GRID_FILLED' if complete else 'GRID_PARTIAL_FILL',
                    交易对=bot.cfg['symbol'],层级='G'+str(rec['layer']),
                    方向='LONG' if rec['body']['orderSide']=='BUY' else 'SHORT',
                    本次新增成交量=str(dec(rec['filled'])-dec(old['filled'])),
                    本层累计成交量=rec['filled'],本层实际成交均价=rec['avg_fill'],
                    最新整仓数量=pos.get('qty','0'),最新整仓均价=pos.get('entry','0'),
                    订单ID=rec['order_id'])
            if rec['role']=='T' and (rec['status']!=old['status'] or rec['terminal']!=old['terminal']
                                    or rec['filled']!=old['filled']):
                terminal_trade_log('TP_STATUS',交易对=bot.cfg['symbol'],状态=rec['status'],
                    终态=rec['terminal'],TP价格=rec['body']['price'],TP数量=rec['body']['quantity'],
                    已成交量=rec['filled'],reduceOnly=rec['body']['reduceOnly'],订单ID=rec['order_id'])
    except Exception:
        pass  # Logging is an observer, never a trading prerequisite.


def bounded_price(market, raw_price, side):
    # Round inward so tick rounding cannot enlarge the configured slippage bound.
    candidate = dec(raw_price)
    for _ in range(8):
        tick = dec(market['tickSize'])
        for tier in market.get('tickTiers', []):
            if 'upToPrice' not in tier or candidate < dec(tier['upToPrice']):
                tick = dec(tier['tick'])
                break
        rounded = (candidate/tick).to_integral_value(rounding=ROUND_DOWN if side == 'BUY' else ROUND_UP)*tick
        if rounded == candidate:
            if rounded <= 0:
                raise SafetyError('限价无效')
            return rounded
        candidate = rounded
    raise SafetyError('无法确定价格档位')

def new_state(identity):
    return dict(version=2,identity=identity,state='WAIT',cycle=None,orders={},ledger={},
                base_qty='0',known_qty='0',sequence=0,managed={},daily={},exiting=False,
                exit_reason='',cooldown_until=0,recovery_required='',last_completed_cycle=None)

def read_state(path, identity):
    if not path.exists():
        return new_state(identity),False
    try:
        s=json.loads(path.read_text())
        if s['version']!=2 or s['identity']!=identity or s['state'] not in STATES:
            raise ValueError()
        for k in new_state(identity):
            if k not in s:
                raise ValueError()
        if not isinstance(s['orders'],dict) or not isinstance(s['ledger'],dict):
            raise ValueError()
        if s['ledger']:
            if (type(s['ledger']['last_signal_bar']) is not int or s['ledger']['last_signal_side'] not in ('LONG','SHORT')
                or not math.isfinite(float(s['ledger']['signal_time']))):
                raise ValueError()
        dec(s['known_qty']); dec(s['base_qty'])
        return s,True
    except (OSError,ValueError,KeyError,TypeError,SafetyError):
        raise SafetyError('持久化状态损坏或账户不匹配；禁止按空仓重新开始') from None

def order_record(body, role, layer, now):
    return dict(body=body,role=role,layer=layer,created_at=now,order_id=None,
                status='INTENT_SAVED',filled='0',avg_fill='0',terminal=False,
                sequence=0,updated_at=0,cancel_requested=False,cancel_time=0)

def telegram_log(reason, **fields):
    # Never log request URLs, response bodies, exception text, token or chat ID.
    try:
        log('TELEGRAM', reason=reason, **fields)
    except Exception:
        pass


def telegram_credentials(cfg):
    if cfg.get('telegram_enabled',False) is not True:
        return '', ''
    token=os.environ.get('ARCUS_TELEGRAM_BOT_TOKEN','').strip() or str(cfg.get('telegram_bot_token') or '').strip()
    chat=os.environ.get('ARCUS_TELEGRAM_CHAT_ID','').strip() or str(cfg.get('telegram_chat_id') or '').strip()
    return token,chat


def send_telegram(message, cfg):
    """One HTTP attempt, called only by the notification worker in production.

    https://core.telegram.org/bots/api#sendmessage
    At-most-once attempts: never retry an ambiguous response or a 429.
    """
    try:
        token,chat=telegram_credentials(cfg)
        if not token or not chat:
            return False
        response=requests.post('https://api.telegram.org/bot'+token+'/sendMessage',
                               json={'chat_id':chat,'text':message}, timeout=(3,5),
                               allow_redirects=False)
        try:
            if response.status_code!=200:
                telegram_log('发送失败，不重试',status=response.status_code)
                return False
            if response.json().get('ok') is not True:
                telegram_log('Telegram API拒绝，不重试')
                return False
            return True
        finally:
            response.close()
    except Exception:
        telegram_log('网络/响应异常，不重试')
        return False


class TelegramNotifications:
    """Passive observer. Worker never touches bot state, exchange or orders."""
    def __init__(self, bot=None, cfg=None):
        self.bot=bot
        self.cfg=bot.cfg if bot is not None else cfg
        self.ready=False
        self.disabled=False
        self.started=False
        self.previous_qty=Decimal('0')
        self.pending_close=None
        self.messages=queue.Queue(maxsize=64)
        self.worker=None

    def safe(self, method, *args):
        try:
            if not self.disabled:
                return getattr(self,method)(*args)
        except Exception:
            # Includes journal/queue failures: notifications stop, trading does not.
            self.disabled=True
            telegram_log('通知旁路异常，本进程停止通知；交易继续')
        return None

    def _enqueue(self, message):
        token,chat=telegram_credentials(self.cfg)
        if not token or not chat:
            return
        if self.worker is None:
            self.worker=threading.Thread(target=self._run,name='arcus-telegram',daemon=True)
            self.worker.start()
        try:
            self.messages.put_nowait(message)
        except queue.Full:
            telegram_log('通知队列已满，丢弃本条且不重试')

    def _run(self):
        while True:
            message=self.messages.get()
            try:
                send_telegram(message,self.cfg)
            except Exception:
                telegram_log('后台通知异常，不重试')
            finally:
                self.messages.task_done()

    def _journal(self):
        journal=self.bot.state.setdefault('telegram',{'version':1,'claimed':{}})
        if (not isinstance(journal,dict) or journal.get('version')!=1
            or not isinstance(journal.get('claimed'),dict)):
            raise ValueError('invalid notification journal')
        return journal['claimed']

    def _key(self, role, layer=0):
        return str(self.bot.state['cycle'])+':'+role+':'+str(layer)

    @staticmethod
    def _complete(rec):
        return (rec['terminal'] and dec(rec['filled'])>0
                and dec(rec['filled'])==dec(rec['body']['quantity']))

    def baseline(self):
        # Recovery is silent even with an old/missing notification journal.
        b=self.bot
        claimed=self._journal()
        for rec in b.state['orders'].values():
            if rec['role'] in ('E','G') and self._complete(rec):
                claimed[self._key(rec['role'],rec['layer'])]='history'
        self.previous_qty=dec(b.position().get('qty',0))
        if not self.previous_qty and b.state['cycle']:
            claimed[self._key('C')]='history'
        b.save()
        self.ready=True

    def _claim_and_enqueue(self, key, message):
        claimed=self._journal()
        if key in claimed:
            return
        # Persist BEFORE enqueue: timeout/crash cannot authorize a second attempt.
        # This favors no duplicates over guaranteed delivery.
        claimed[key]='attempted'
        self.bot.save()
        self._enqueue(message)

    @staticmethod
    def _time():
        return datetime.now().astimezone().strftime('%Y-%m-%d %H:%M')

    def startup(self, state=None):
        if self.started:
            return
        self.started=True
        if self.bot is not None:
            if not self.ready:
                return
            state=self.bot.state['state']
        timestamp=datetime.now().astimezone().strftime('%Y-%m-%d %H:%M')
        adopted=''
        if self.bot is not None and self.bot.state['managed'].get('adopted_g0') and self.bot.position():
            side='LONG' if dec(self.bot.position()['qty'])>0 else 'SHORT'
            adopted=f"\n检测已有仓位：{side}\n接管状态：已自动接管"
        self._enqueue(f"Arcus双币种对冲机器人启动\n交易对：{'BTC对冲ETH' if self.cfg.get('hedge_enabled') else self.cfg['symbol']}{adopted}\n时间：{timestamp}")

    def observe(self):
        # Called only AFTER successful REST/WS reconciliation and its state save.
        b=self.bot
        if not self.ready or b.cfg['dry_run'] or b.state.get('recovery_required'):
            return
        pos=b.position()
        qty=dec(pos.get('qty',0))
        if qty:
            for rec in b.state['orders'].values():
                if rec['role'] not in ('E','G') or not self._complete(rec):
                    continue
                key=self._key(rec['role'],rec['layer'])
                if key in self._journal():
                    continue
                side='LONG' if rec['body']['orderSide']=='BUY' else 'SHORT'
                if rec['role']=='E':
                    title='🟢 首仓成交' if side=='LONG' else '🔴 首仓成交'
                    message=f"{title}\n\n方向：{side}\n交易对：{b.cfg['symbol']}\n成交价：{rec['avg_fill']}"
                else:
                    message=(f"🔵 网格补仓成交\n\n方向：{side}\n交易对：{b.cfg['symbol']}"
                             f"\n层级：G{rec['layer']} / G{b.cfg['grid_max_layers']}\n本层成交价：{rec['avg_fill']}"
                             f"\n最新整仓均价：{pos['entry']}\n重新计算止盈（由现有D4处理）")
                self._claim_and_enqueue(key,message+f"\n时间：{self._time()}")
        if self.previous_qty and not qty and b.state['cycle']:
            closes=[r for r in b.state['orders'].values() if r['role'] in ('T','X') and dec(r['filled'])>0]
            last=max(closes,key=lambda r:r['updated_at']) if closes else None
            reason=b.state['exit_reason']
            kind='SL' if reason=='价格止损' else 'TP' if (last and last['role']=='T') or reason in ('盈利回撤退出','分层固定止盈') else '其他'
            side='LONG' if self.previous_qty>0 else 'SHORT'
            price=last['avg_fill']+'（最后平仓订单成交均价）' if last else '无法可靠取得'
            self.pending_close=(b.state['cycle'],self._key('C'),
                                f"✅ 本轮交易结束\n\n方向：{side}\n交易对：{b.cfg['symbol']}"
                                f"\n平仓类型：{kind}\n平仓价：{price}\n本轮最终状态：WAIT")
        self.previous_qty=qty

    def finished(self):
        # Existing finish_cycle already confirmed zero position + no live orders,
        # cleared the cycle and persisted WAIT before this observer is called.
        b=self.bot
        if not self.ready or not self.pending_close or b.cfg['dry_run']:
            return
        cycle,key,message=self.pending_close
        if (b.state['last_completed_cycle']!=cycle or b.state['state']!='WAIT'
            or dec(b.position().get('qty',0)) or b.orders.active()):
            return
        self._claim_and_enqueue(key,message+f"\n时间：{self._time()}")
        self.pending_close=None


def acquire_process_lock(lock):
    try:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        raise SafetyError('同一账户/模式已有程序运行') from None


class BotState:
    def __init__(self, cfg, client, stream, path, emit=log):
        self.cfg,self.client,self.stream,self.path=cfg,client,stream,Path(path)
        self.emit=emit
        self.identity=dict(network=cfg['network'],address=client.address,account_index=client.account_index,
                           symbol=cfg['symbol'],prefix=cfg['bot_prefix'],dry_run=cfg['dry_run'])
        self.state,self.had_state=read_state(self.path,self.identity)
        self.market=None
        self.account=None

    def save(self):
        atomic_json(self.path,self.state)


    def position(self):
        return self.account['positions'].get(self.cfg['symbol'],{})


    def set_position_state(self):
        qty=dec(self.position().get('qty',0))
        if self.state['exiting']:
            self.state['state']='EXITING'
        elif qty:
            self.state['state']='GRID_LONG' if qty>0 else 'GRID_SHORT'
        else:
            pending=self.orders.active({'E'})
            self.state['state']=('LONG_ORDER_PENDING' if pending[0]['body']['orderSide']=='BUY' else 'SHORT_ORDER_PENDING') if pending else 'WAIT'


# ============================================================
# D1 信号模块
# ============================================================

def safe_float(v: Any, default: float = 0.0) -> float:
    try:
        return float(v)
    except Exception:
        return default

def calc_rsi(closes: List[float], period: int = 14) -> Optional[float]:
    """Wilder RSI; caller supplies validated closed candles only."""
    values = [safe_float(x, 0.0) for x in (closes or []) if safe_float(x, 0.0) > 0]
    if len(values) < period + 1:
        return None
    deltas = [float(values[i]) - float(values[i - 1]) for i in range(1, len(values))]
    if not deltas:
        return None
    effective_period = max(1, min(int(period or 14), len(deltas)))
    gains = [max(delta, 0.0) for delta in deltas]
    losses = [max(-delta, 0.0) for delta in deltas]
    avg_gain = sum(gains[:effective_period]) / effective_period
    avg_loss = sum(losses[:effective_period]) / effective_period
    for gain, loss in zip(gains[effective_period:], losses[effective_period:]):
        avg_gain = ((avg_gain * (effective_period - 1)) + gain) / effective_period
        avg_loss = ((avg_loss * (effective_period - 1)) + loss) / effective_period
    if avg_loss <= 0:
        return 100.0 if avg_gain > 0 else 50.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))

def calc_ema_series(closes: List[float], period: int) -> List[float]:
    if period <= 1 or not closes:
        return [safe_float(x, 0.0) for x in closes]
    alpha = 2.0 / (float(period) + 1.0)
    out: List[float] = []
    ema: Optional[float] = None
    for price in closes:
        px = safe_float(price, 0.0)
        ema = px if ema is None else (px * alpha + ema * (1.0 - alpha))
        out.append(float(ema))
    return out

def calc_adx(highs, lows, closes, period=14):
    """Wilder ADX. Corrects the skipped smoothing sample in old David.py."""
    if len(closes) < 2 * period + 1:
        return None
    trs, plus, minus = [], [], []
    for i in range(1, len(closes)):
        up, down = highs[i] - highs[i-1], lows[i-1] - lows[i]
        trs.append(max(highs[i]-lows[i], abs(highs[i]-closes[i-1]), abs(lows[i]-closes[i-1])))
        plus.append(up if up > down and up > 0 else 0.0)
        minus.append(down if down > up and down > 0 else 0.0)
    atr, pdm, mdm = sum(trs[:period]), sum(plus[:period]), sum(minus[:period])
    dxs = []
    for i in range(period-1, len(trs)):
        if i >= period:
            atr = atr - atr/period + trs[i]
            pdm = pdm - pdm/period + plus[i]
            mdm = mdm - mdm/period + minus[i]
        pdi, mdi = (100*pdm/atr, 100*mdm/atr) if atr else (0,0)
        dxs.append(100*abs(pdi-mdi)/(pdi+mdi) if pdi+mdi else 0.0)
    adx = sum(dxs[:period])/period
    for dx in dxs[period:]:
        adx = (adx*(period-1)+dx)/period
    return adx

def closed_rows(raw, seconds, minimum, now):
    if not isinstance(raw, list):
        raise ValueError('K线格式无效')
    rows = []
    for r in raw:
        start = int(r['openTime']) / 1e6  # Arcus epoch microseconds
        if r.get('isFinal') is not True or start + seconds > now:
            continue
        v = {k: float(r[k]) for k in ('open', 'high', 'low', 'close')}
        if any(not math.isfinite(x) or x <= 0 for x in v.values()):
            raise ValueError('K线价格无效')
        if v['low'] > min(v['open'], v['close']) or v['high'] < max(v['open'], v['close']):
            raise ValueError('K线高低价无效')
        if start % seconds != 0:
            raise ValueError('K线时间未对齐')
        rows.append(dict(v, time=int(start)))
    rows.sort(key=lambda r: r['time'])
    if len(rows) < minimum:
        raise ValueError('已收盘K线不足')
    if rows[-1]['time'] != int(now // seconds) * seconds - seconds:
        raise ValueError('最新已收盘K线缺失或过期')
    if any(b['time'] - a['time'] != seconds for a, b in zip(rows, rows[1:])):
        raise ValueError('K线缺失或重复')
    return rows

def signal_seen(ledger, bar):
    """Deduplicate 5M signals, accepting persisted records from the old strategy."""
    if not ledger:
        return False
    last = ledger.get('last_signal_bar_5m', ledger.get('last_signal_bar'))
    if type(last) is not int or last % 300:
        raise ValueError('5M信号去重记录无效，禁止产生首仓信号')
    return bar <= last


def evaluate(hourly, entry, cfg, *, five=None, ledger=None, position_side='', has_entry_order=False,
             account_known=False, current_price=None, now=None):
    validate_config(cfg)
    now = time.time() if now is None else now
    ledger = {} if ledger is None else ledger
    result = dict(side='', trend='', state='WAIT', grid_state=None, watch_state=None,
                  signal=False, reason='', price=current_price, trend_close=None,
                  ema_fast=None, ema_slow=None, adx=None, rsi=None, rsi_previous=None,
                  bar=None, bar_5m=None, rsi_5m=None, rsi_previous_5m=None,
                  long_5m=False, short_5m=False,
                  transitions=['WAIT'], order_intent=None)
    try:
        # Legacy hourly argument is ignored; only closed 5M candles drive entry.
        rows = closed_rows(five if five is not None else entry, 300, cfg['rsi_period']+2, now)
        closes = [r['close'] for r in rows]
        rsi = calc_rsi(closes, cfg['rsi_period'])
        prev = calc_rsi(closes[:-1], cfg['rsi_period'])
        long_threshold=cfg.get('rsi_long_threshold',30)
        short_threshold=cfg.get('rsi_short_threshold',70)
        long_5m = prev <= long_threshold and rsi > long_threshold
        short_5m = prev >= short_threshold and rsi < short_threshold
        side = 'LONG' if long_5m else 'SHORT' if short_5m else ''
        result.update(rsi=rsi, rsi_previous=prev, bar=rows[-1]['time'],
                      rsi_5m=rsi, rsi_previous_5m=prev, bar_5m=rows[-1]['time'],
                      long_5m=long_5m, short_5m=short_5m)
        if not account_known:
            result['reason'] = '账户持仓/挂单状态未确认'
        elif position_side:
            if position_side not in ('LONG', 'SHORT'):
                raise ValueError('仓位方向无效')
            result.update(reason='已存在当前网格仓位', grid_state='GRID_'+position_side)
        elif has_entry_order:
            result['reason'] = '已经存在有效首仓挂单'
        else:
            if not side:
                result['reason'] = '5M RSI未发生有效回穿'
            elif signal_seen(ledger,result['bar_5m']):
                result['reason'] = '该5M K线已发出信号或时间回退'
            else:
                ledger.update(last_signal_bar=result['bar'], last_signal_bar_5m=result['bar_5m'],
                              last_signal_side=side, signal_time=now)
                result.update(side=side, state=side+'_ORDER_PENDING', signal=True,
                              reason=f"5M RSI{cfg['rsi_period']}向上回穿{long_threshold:g}" if side == 'LONG' else f"5M RSI{cfg['rsi_period']}向下回穿{short_threshold:g}",
                              order_intent=dict(side='BUY' if side == 'LONG' else 'SELL',
                                                type='LIMIT', relative_price='BELOW' if side == 'LONG' else 'ABOVE',
                                                submitted=False))
                result['transitions'] += [side+'_SIGNAL', side+'_ORDER_PENDING']
        if not result['signal'] and result['transitions'][-1] != 'WAIT':
            result['transitions'].append('WAIT')
    except (ValueError, TypeError, KeyError, OverflowError) as exc:
        result['reason'] = '数据不可用：' + str(exc)
    return result

def format_log(symbol, r, cfg):
    if cfg.get('hedge_enabled'):
        value='N/A' if r['rsi_5m'] is None else f"{r['rsi_5m']:.2f}"
        return (f"BTC 5M RSI12={value} | LONG条件={str(r['long_signal']).upper()}"
                f" | SHORT条件={str(r['short_signal']).upper()} | 开仓方向={r['side'] or 'NONE'}")
    def fmt(x):
        return 'N/A' if x is None else f'{float(x):.4f}'
    return (f"[SIGNAL] {symbol} | 当前价格={fmt(r['price'])}"
            f" | 5M RSI{cfg['rsi_period']}当前={fmt(r['rsi_5m'])} | 5M RSI前值={fmt(r['rsi_previous_5m'])}"
            f" | 5M回升穿过{cfg.get('rsi_long_threshold',30):g}={str(r['long_5m']).upper()} | 5M回落穿过{cfg.get('rsi_short_threshold',70):g}={str(r['short_5m']).upper()}"
            f" | 状态={r['state']}"
            f" | 开仓信号={str(r['signal']).upper()} | 原因={r['reason']}")

# ============================================================
# D2 开仓挂单模块
# ============================================================

class EntryManager:
    def __init__(self, bot):
        self.bot = bot

    def expire_pending(self):
        b = self.bot
        for rec in b.orders.active({'E'}):
            if b.client.now()-rec['created_at']>=b.cfg['entry_timeout_sec'] or b.state['daily']['halted']:
                b.orders.cancel(rec)

    def tick(self, r, q):
        b = self.bot
        pending=b.orders.active({'E'})
        if pending:
            for rec in pending:
                if b.client.now()-rec['created_at']>=b.cfg['entry_timeout_sec'] or b.state['daily']['halted']:
                    b.orders.cancel(rec)
            return
        if not r['signal'] or b.client.now()<b.state['cooldown_until'] or b.state['daily']['halted']:
            return
        problems=live_blockers(b.cfg)
        if problems:
            raise SafetyError('; '.join(problems))
        b.check_open_risk(q)
        # Refresh account and quote immediately before creating the journaled intent.
        b.reconcile()
        if b.position() or b.orders.active():
            return
        q=b.client.quote()
        if abs(q['mid']/dec(r['price'])-1)>dec(b.cfg['max_signal_price_deviation_pct']):
            raise SafetyError('信号至提交期间价格偏离过大')
        side='BUY' if r['side']=='LONG' else 'SELL'
        raw=q['mid']*(1-dec(b.cfg['entry_limit_offset_pct']) if side=='BUY' else 1+dec(b.cfg['entry_limit_offset_pct']))
        price=bounded_price(b.market,raw,side)
        if (side=='BUY' and price>=q['bid']) or (side=='SELL' and price<=q['ask']):
            raise SafetyError('挂单距离/精度不足以位于当前盘口外侧，不自动改变距离')
        qty=opening_quantity(b.cfg,b.account,{},b.market,q,price,b.cfg['first_order_size'])
        b.state.update(cycle=f"{r['bar']:08x}{uuid.uuid4().hex[:6]}",state=r['state'])
        b.save()
        b.orders.submit('E',0,side,qty,price,'ALO',False)
        b.save()


# ============================================================
# D3 网格补仓模块
# ============================================================

def legacy_grid_decision(position, managed, sig, quote_data, cfg, now):
    """Original Arcus01 adverse gap + trend + reversal gate, no new indicators.
    NEED_CONFIRMATION: old five-minute gate vs requested fixed resting grid.
    Choosing legacy_dynamic explicitly selects this old execution policy.
    """
    layer=max(1,int(managed.get('layers',1)))
    if layer>=cfg['grid_max_layers']+1 or not sig:
        return False
    qty,entry=dec(position['qty']),dec(position['entry'])
    side='LONG' if qty>0 else 'SHORT'
    executable=quote_data['bid'] if qty>0 else quote_data['ask']
    last=dec(managed.get('last_fill_price',entry))
    adverse=float((last-executable)/last*(1 if qty>0 else -1))
    mult=max(cfg['legacy_gap_multiplier_min'],min(cfg['legacy_gap_multiplier_max'],
             sig['volatility']/cfg['legacy_volatility_base']))
    gap=cfg['grid_spacing']*mult
    return (sig['trend']==side and sig['reversal_long' if qty>0 else 'reversal_short']
            and adverse>=gap and now-managed.get('last_trade_time',now)>=cfg['add_cooldown_seconds']
            and sig['bar']!=managed.get('last_entry_bar'))

def legacy_grid_inputs(hourly, five, cfg, now):
    """Preserve old grid trend filtering as an explicit legacy-only conflict.
    The prior trend also required EMA120, path efficiency, and 1H RSI.
    Those contradict the user's three-indicator first-entry specification;
    we do NOT silently replace their meaning with the new trend signal.
    """
    raise SafetyError('NEED_CONFIRMATION: 旧补仓trend含EMA120/路径效率/1H RSI；需确认是否改用新1H趋势，不能默改旧算法')

class GridManager:
    def __init__(self, bot):
        self.bot=bot

    def tick(self, q):
        b=self.bot
        if not b.cfg.get('grid_enabled',True) or b.cfg.get('hedge_enabled'):
            return
        if b.state.get('recovery_required'):
            raise SafetyError(b.state['recovery_required'])
        if b.cfg['grid_mode'] is None:
            raise SafetyError('NEED_CONFIRMATION: grid_mode 未选择')
        if b.orders.active({'E','G'}) or b.state['exiting'] or b.risk.daily_halt_blocks_management():
            return
        pos=b.position()
        completed=[r for r in b.state['orders'].values() if r['role'] in ('E','G') and dec(r['filled'])>0]
        adopted=b.state['managed'].get('adopted_g0')
        layer=max((r['layer'] for r in completed),default=0 if adopted else -1)+1
        if layer<1 or layer>b.cfg['grid_max_layers']:
            return
        if any(r['role']=='G' and r['layer']==layer for r in b.state['orders'].values()):
            return  # Rejection/cancel is recorded, never silently replace same layer.
        if b.cfg['grid_mode']=='fixed':
            # A canceled partial fill is not a completed layer. Do not skip gaps
            # or infer completion from a nonzero filled amount after restart.
            for previous_layer in range(1 if adopted else 0,layer):
                previous=[r for r in completed if r['layer']==previous_layer]
                if (len(previous)!=1 or not previous[0]['terminal']
                    or dec(previous[0]['filled'])!=dec(previous[0]['body']['quantity'])):
                    return
        side='BUY' if dec(pos['qty'])>0 else 'SELL'
        anchor=dec(b.state['managed']['last_fill_price'])
        if b.cfg['grid_mode']=='legacy_dynamic':
            sig=legacy_grid_inputs(b.client.candles('1h'),b.client.candles('5m'),b.cfg,b.client.now())
            if not legacy_grid_decision(pos,b.state['managed'],sig,q,b.cfg,b.client.now()):
                return
            # Original execution was an aggressive LIMIT IOC, not a resting grid.
            price=exit_limit(q,side,b.cfg,b.market)
            tif='IOC'
        else:
            spacing=dec(b.cfg['grid_spacings'][layer-1])
            raw=anchor*(1-spacing if side=='BUY' else 1+spacing)
            price=bounded_price(b.market,raw,side)
            tif='ALO'
            if (side=='BUY' and price>=q['ask']) or (side=='SELL' and price<=q['bid']):
                log('GRID_WAIT',reason='目标网格价已跨盘口；不自动追价或改变挂单价')
                return
        b.check_open_risk(q)
        qty=opening_quantity(b.cfg,b.account,pos,b.market,q,price,b.cfg['grid_order_sizes'][layer-1])
        b.orders.submit('G',layer,side,qty,price,tif)

# ============================================================
# D4 止盈/止损模块
# ============================================================

def exit_limit(q, side, cfg, market):
    reference=q['ask'] if side=='BUY' else q['bid']
    raw=reference*(1+dec(cfg['max_slippage_bps'])/10000*(1 if side=='BUY' else -1))
    price=bounded_price(market,raw,side)
    if (side=='BUY' and price<q['ask']) or (side=='SELL' and price>q['bid']):
        raise SafetyError('价格档位无法满足平仓滑点上限')
    return price

def legacy_exit_reason(position, managed, q, cfg):
    """Preserved legacy fixed/trailing profit gates; true exchange qty/entry."""
    qty,entry=dec(position['qty']),dec(position['entry'])
    executable=q['bid'] if qty>0 else q['ask']
    pnl=float((executable/entry-1)*(1 if qty>0 else -1))
    if managed.get('closing_reason'):
        return managed['closing_reason']
    if pnl<=-cfg['stop_loss_pct']:
        return '价格止损'
    layer=max(1,int(managed.get('layers',1)))
    target=cfg['take_profit_by_layer'][min(layer,len(cfg['take_profit_by_layer']))-1]
    drawdown=cfg['trailing_drawdown_by_layer'][min(layer,len(cfg['trailing_drawdown_by_layer']))-1]
    peak=max(float(managed.get('peak_pnl',0)),pnl)
    managed['peak_pnl']=peak
    if pnl>=target:
        managed['tp_armed']=True
    gross=float(abs(qty)*entry)*pnl
    estimated_net=gross-float(abs(qty)*executable)*cfg['fee_buffer_bps']/10000
    if drawdown==0 and pnl>=target and estimated_net>=cfg['min_profit_usd']:
        return '分层固定止盈'
    if drawdown>0 and managed.get('tp_armed') and peak-pnl>=drawdown:
        return '盈利回撤退出'
    return ''

def tp_pct_for_grid_layer(cfg, grid_layer):
    """Fixed resting TP for the last fully filled grid layer, G0 through G5."""
    if type(grid_layer) is not int or not 0 <= grid_layer <= 5:
        raise SafetyError('TP网格层级无效，不能猜测止盈档位')
    tiers=cfg.get('take_profit_pct_by_grid_layer')
    if not isinstance(tiers,list) or len(tiers)!=6:
        raise SafetyError('缺少G0至G5整仓TP档位配置')
    pct=dec(tiers[grid_layer])
    if not 0 < pct < 1:
        raise SafetyError('TP百分比必须大于0且小于1')
    return pct


class TakeProfitManager:
    def __init__(self, bot):
        self.bot=bot

    def target(self, pos):
        b=self.bot
        pct=tp_pct_for_grid_layer(b.cfg,b.state['managed'].get('grid_layer',0))
        long=dec(pos['qty'])>0
        raw=dec(pos['entry'])*(1+dec(pct)*(1 if long else -1))
        # Round away from entry so a tick never undercuts the chosen TP percentage.
        return bounded_price(b.market,raw,'SELL' if long else 'BUY')

    def tick(self, q):
        b=self.bot
        pos=b.position()
        if not pos:
            return
        if b.cfg['tp_mode'] is None:
            raise SafetyError('NEED_CONFIRMATION: tp_mode 未选择')
        if b.cfg['tp_mode']=='legacy_layered':
            if b.state.get('recovery_required'):
                raise SafetyError('恢复仓位层数未知，不能推断分层/回撤止盈参数')
            reason=legacy_exit_reason(pos,b.state['managed'],q,b.cfg)
            b.save()
            if reason:
                b.begin_exit(reason)
            return
        price=self.target(pos)
        qty=abs(dec(pos['qty']))
        side='SELL' if dec(pos['qty'])>0 else 'BUY'
        # Slice only if exchange maxOrderSize requires it; remainder stays managed.
        qty=min(qty,dec(b.market['maxOrderSize']))
        if qty!=floor_step(qty,b.market['stepSize']):
            raise SafetyError('真实仓位含不可下单尾数，不舍弃仓位')
        active=b.orders.active({'T','X'})
        if active:
            r=active[0]
            if (r['role']=='T' and not r['cancel_requested'] and dec(r['body']['price'])==price
                and dec(r['body']['quantity'])-dec(r['filled'])==qty):
                return
            for r in active:
                b.orders.cancel(r)
            return  # Re-read orders AND account before placing replacement.
        if b.orders.active({'E','G'}) and any(r['status'] in ('INTENT_SAVED','OUTCOME_UNKNOWN','ACK_ONLY') for r in b.orders.active({'E','G'})):
            return
        b.orders.submit('T',0,side,qty,price,'GTT',True)

class ExitManager:
    def __init__(self, bot):
        self.bot = bot

    def begin_exit(self, reason):
        b = self.bot
        b.state.update(exiting=True,state='EXITING',exit_reason=reason)
        b.state['managed']['closing_reason']=reason
        b.save()


    def finish_cycle(self):
        b = self.bot
        # Only after all old orders are terminal and exchange position is flat.
        if b.position() or b.orders.active():
            return False
        b.state.update(last_completed_cycle=b.state['cycle'],cycle=None,orders={},base_qty='0',known_qty='0',
                          managed={},exiting=False,exit_reason='',state='WAIT',recovery_required='',
                          cooldown_until=b.client.now()+b.cfg['cooldown_seconds'])
        b.save()  # Keep ledger across all cycles so the same signal cannot reopen.
        return True


    def exit_tick(self,q):
        b = self.bot
        # Cancel all exposure orders first; no new TP/close while cancellation uncertain.
        exposure=b.orders.active({'E','G'})
        for r in exposure:
            b.orders.cancel(r)
        if exposure:
            return
        pos=b.position()
        closes=b.orders.active({'T','X'})
        if not pos:
            for r in closes:
                b.orders.cancel(r)
            if not closes:
                b.finish_cycle()
            return
        # An existing partially-filled TP may finish naturally, unless risk exit demands replacement.
        urgent=b.state['exit_reason'] in ('价格止损','日内亏损限制','盈利回撤退出','分层固定止盈')
        if closes:
            if urgent:
                for r in closes:
                    b.orders.cancel(r)
            elif b.cfg['tp_mode']=='fixed_limit':
                b.tp.tick(q)
            return
        if b.state['exit_reason']=='止盈/平仓已有真实成交，结束本轮' and b.cfg['tp_mode']=='fixed_limit':
            b.tp.tick(q)
            return
        side='SELL' if dec(pos['qty'])>0 else 'BUY'
        qty=min(abs(dec(pos['qty'])),dec(b.market['maxOrderSize']))
        b.orders.submit('X',0,side,qty,exit_limit(q,side,b.cfg,b.market),'IOC',True)


    def check_triggers(self, q, pos):
        b = self.bot
        if pos:
            pnl=(q['bid']/dec(pos['entry'])-1) if dec(pos['qty'])>0 else (1-q['ask']/dec(pos['entry']))
            if pnl<=-dec(b.cfg['stop_loss_pct']):
                b.begin_exit('价格止损')
            elif b.risk.daily_halt_blocks_management():
                b.begin_exit('日内亏损限制')
        elif b.state['cycle'] and not b.orders.active({'E'}):
            b.begin_exit(b.state['exit_reason'] or '空仓收尾')

# ============================================================
# D5 风控/恢复模块
# ============================================================

class UnknownOutcome(SafetyError):
    """A write may have reached the engine. Never resubmit a placement."""

class ApiError(SafetyError):
    def __init__(self, status, message):
        self.status = status
        super().__init__(message)

def live_blockers(cfg):
    problems=[]
    if cfg.get('sizing_confirmed') is not True:
        problems.append('NEED_CONFIRMATION: 保证金总额单位及首仓/两次补仓分配未确认')
    if cfg['entry_limit_offset_pct'] is None:
        problems.append('NEED_CONFIRMATION: entry_limit_offset_pct 未填写')
    if cfg['grid_mode'] is None:
        problems.append('NEED_CONFIRMATION: grid_mode（旧动态补仓或固定网格）')
    elif cfg['grid_mode']=='legacy_dynamic':
        problems.append('NEED_CONFIRMATION: 旧补仓趋势输入与三指标约束冲突，尚未授权替换')
    if cfg['tp_mode'] is None:
        problems.append('NEED_CONFIRMATION: tp_mode（旧分层/回撤或固定常驻TP）')
    if cfg['tp_mode']=='fixed_limit' and cfg['take_profit_pct'] is None:
        problems.append('NEED_CONFIRMATION: take_profit_pct 未填写')
    return problems

def canonical(value):
    return json.dumps(value, separators=(',', ':'), sort_keys=True, ensure_ascii=True).encode()

def order_payload(body, market):
    def integer(value, unit):
        n = dec(value)/dec(unit)
        if n != n.to_integral_value():
            raise SafetyError('订单价格/数量不符合交易精度')
        return int(n)
    payload = {'ad': body['address'].lower(), 'ai': body['accountIndex'],
               'ct': int(body['timestamp']), 'g': int(body['goodTilTime'])*1000,
               'm': body['marketId'], 'op': 1, 'p': integer(body['price'], market['tickSize']),
               'q': integer(body['quantity'], market['stepSize']), 'r': int(body['reduceOnly']),
               's': {'BUY': 0, 'SELL': 1}[body['orderSide']],
               't': {'GTT':0,'FOK':1,'IOC':2,'ALO':3}[body['timeInForce']], 'v': 1}
    if body.get('clientId'):
        payload['c'] = body['clientId']
    return payload

def parse_account(data, address, account_index):
    if not isinstance(data, dict) or not isinstance(data.get('positions'), dict):
        raise SafetyError('账户接口格式异常，不按空仓处理')
    if str(data.get('address', '')).lower() != address.lower() or data.get('accountIndex') != account_index:
        raise SafetyError('账户身份不匹配')
    equity, free, deposits = dec(data['equity']), dec(data['freeCollateral']), dec(data['netDeposits'])
    seq = int(data['sequenceNumber'])
    positions = {}
    for mid, p in data['positions'].items():
        if not isinstance(p, dict) or int(p['marketId']) != int(mid):
            raise SafetyError('持仓 marketId 不匹配')
        if str(p.get('address', '')).lower() != address.lower() or p.get('accountIndex') != account_index:
            raise SafetyError('持仓账户不匹配')
        qty = dec(p['size'])
        if not qty:
            continue
        if (qty > 0 and p['side'] != 'LONG') or (qty < 0 and p['side'] != 'SHORT'):
            raise SafetyError('持仓数量与方向不一致')
        entry, mark, notional = dec(p['averageEntryPrice']), dec(p['markPx']), abs(dec(p['positionValueNotional']))
        if entry <= 0 or mark <= 0 or notional <= 0:
            raise SafetyError('持仓价格/名义金额异常')
        # Reject scale/schema errors rather than guessing engine atom conversion.
        calculated = abs(qty)*mark
        if abs(calculated-notional)/max(calculated, notional) > dec('0.02'):
            raise SafetyError('持仓数量与名义金额量纲不一致')
        positions[p['marketDisplayName']] = {'qty': str(qty), 'entry': str(entry), 'mark': str(mark),
                                              'notional': str(notional), 'market_id': int(mid)}
    return {'equity': str(equity), 'free': str(free), 'deposits': str(deposits),
            'sequence': seq, 'positions': positions}

class ArcusClient:
    def __init__(self, cfg):
        self.cfg=cfg
        self.base='https://api.arcus.xyz' if cfg['network']=='mainnet' else 'https://api.testnet.arcus.xyz'
        self.ws_url=self.base.replace('https:', 'wss:')+'/v1/ws'
        self.address=credential_value(cfg,'wallet_address','wallet_address_env').lower()
        self.account_index=cfg['account_index']
        self.session=requests.Session()
        self.session.headers['User-Agent']='ArcusSingleFile/2'
        self.key=None
        self.api_key=None
        self.clock_ns=None
        self.clock_mono=None
        self.last_nonce=0
        self.cooldown_until=0

    def account_params(self):
        if not re.fullmatch(r'0x[0-9a-f]{40}',self.address):
            raise SafetyError('请填写config.json的wallet_address，或设置环境变量 '+self.cfg['wallet_address_env'])
        return {'address':self.address, 'accountIndex':self.account_index}

    def request(self, method, path, params=None, body=None, headers=None):
        if method!='GET' and self.cfg['dry_run']:
            raise SafetyError('dry_run禁止任何交易所写入')
        if time.monotonic()<self.cooldown_until:
            raise SafetyError('API限流退避中')
        attempts=self.cfg['read_retries'] if method=='GET' else 1
        for attempt in range(attempts):
            try:
                r=self.session.request(method,self.base+path,params=params,json=body,
                                       headers=headers,timeout=self.cfg['request_timeout_sec'],allow_redirects=False)
            except requests.RequestException:
                if method!='GET':
                    raise UnknownOutcome('网络异常，订单结果未知；只查询，不重复提交') from None
                if attempt+1<attempts:
                    time.sleep(self.cfg['retry_backoff_sec']*(attempt+1))
                    continue
                raise SafetyError('Arcus只读请求网络失败：'+path) from None
            if r.status_code==429:
                try:
                    delay=max(float(r.headers.get('Retry-After',0)),float(r.json().get('retryAfterMs',0))/1000)
                except (ValueError,TypeError):
                    delay=self.cfg['retry_backoff_sec']
                self.cooldown_until=time.monotonic()+max(delay,self.cfg['retry_backoff_sec'])
            if r.status_code not in (200,202):
                if method!='GET':
                    raise UnknownOutcome(f'Arcus写入HTTP {r.status_code}；持久化意图保留，禁止重发')
                if r.status_code>=500 and attempt+1<attempts:
                    time.sleep(self.cfg['retry_backoff_sec']*(attempt+1))
                    continue
                raise ApiError(r.status_code,f'Arcus读取HTTP {r.status_code}：{path}')
            try:
                data=r.json()
            except ValueError:
                if method!='GET':
                    raise UnknownOutcome('写入响应无法解析，禁止重发') from None
                raise SafetyError('Arcus返回非JSON') from None
            if not isinstance(data,dict) or data.get('error'):
                if method!='GET':
                    raise UnknownOutcome('写入响应未知，禁止重发')
                raise SafetyError('Arcus响应格式无效')
            return data
        raise SafetyError('请求失败')

    def sync_time(self):
        for attempt in range(self.cfg['read_retries']):
            start=time.monotonic_ns()
            response=self.request('GET','/v1/time')
            end=time.monotonic_ns()
            ns=int(response['timeNs'])
            if ns<10**18:
                raise SafetyError('服务器时间不是Unix纳秒')
            rtt=(end-start)/1e9
            if rtt<=self.cfg['max_clock_rtt_sec']:
                # Conservative server lower bound for closed candles (never early-close).
                self.clock_ns=ns
                self.clock_mono=end
                return ns/1e9
            if attempt+1<self.cfg['read_retries']:
                time.sleep(self.cfg['retry_backoff_sec'])
        raise SafetyError(f'服务器时间往返延迟{rtt:.2f}s超过配置上限；未放宽时间校验')

    def now_ns(self):
        if self.clock_ns is None or (time.monotonic_ns()-self.clock_mono)/1e9>self.cfg['clock_refresh_sec']:
            self.sync_time()
        return self.clock_ns+time.monotonic_ns()-self.clock_mono

    def now(self):
        return self.now_ns()/1e9

    def nonce(self):
        self.last_nonce=max(self.last_nonce+1,self.now_ns())
        return self.last_nonce

    def load_signer(self):
        raw=credential_value(self.cfg,'api_signing_key','signing_key_env').removeprefix('0x')
        if not re.fullmatch('[a-fA-F0-9]{64}',raw):
            raise SafetyError('请填写config.json的api_signing_key或对应环境变量，内容为Ed25519 API Signing Key，不是钱包私钥')
        self.key=Ed25519PrivateKey.from_private_bytes(bytes.fromhex(raw))
        self.api_key=self.key.public_key().public_bytes(Encoding.Raw,PublicFormat.Raw).hex()
        self.session.headers['X-API-Key']=self.api_key

    def verify_key(self):
        self.account_params()
        rows=self.request('GET','/v1/apiKeys',{'address':self.address})['apiKeys']
        matches=[k for k in rows if k.get('apiKey')==self.api_key and k.get('status')=='ACTIVE'
                 and (k.get('allSubaccounts') is True or k.get('accountIndex')==self.account_index)]
        if len(matches)!=1 or (int(matches[0]['validUntil'])!=0 and int(matches[0]['validUntil'])<=self.now()*1000):
            raise SafetyError('API密钥授权、子账户或有效期不符合要求')

    def signed_headers(self, ts, payload):
        if self.key is None:
            raise SafetyError('尚未加载API签名密钥')
        return {'X-API-Key':self.api_key,'X-Timestamp':str(ts),'X-Signature':self.key.sign(canonical(payload)).hex()}

    def market(self, symbol=None):
        symbol=symbol or self.cfg['symbol']
        rows=self.request('GET','/v1/markets')['markets']
        matches=[m for m in rows if m['marketDisplayName']==symbol]
        if len(matches)!=1:
            raise SafetyError('未找到唯一市场：'+symbol)
        m=matches[0]
        for k in ('tickSize','stepSize','minOrderSize','maxOrderSize','minOrderNotional'):
            if dec(m[k])<=0:
                raise SafetyError('市场精度/数量限制无效：'+k)
        return m

    def quote(self, symbol=None):
        data=self.request('GET','/v1/bbo/'+quote(symbol or self.cfg['symbol'],safe=''))
        age=self.now()-int(data['timestamp'])/1e6
        if not -self.cfg['max_clock_rtt_sec']<=age<=self.cfg['quote_max_age_seconds']:
            raise SafetyError('报价过期')
        bid,ask=dec(data['bestBid']['price']),dec(data['bestAsk']['price'])
        if not 0<bid<=ask:
            raise SafetyError('报价无效')
        return {'bid':bid,'ask':ask,'mid':(bid+ask)/2}

    def candles(self, timeframe):
        return self.request('GET','/v1/candles',{'market':self.cfg['symbol'],'timeframe':timeframe,
                            'to':self.now_ns()//1000,'countback':self.cfg['candle_count']})['candles']

    def account(self):
        return parse_account(self.request('GET','/v1/account',self.account_params(),
                            headers={'Cache-Control':'no-cache','Pragma':'no-cache'}),self.address,self.account_index)

    def _orders(self, path, time_field, start=None, symbol=None):
        page_size=self.cfg['history_page_size']
        params={**self.account_params(),'market':symbol or self.cfg['symbol'],'limit':page_size}
        if start is not None:
            params['from']=int(start)
        result={}
        last_bound=None
        for _ in range(self.cfg['history_max_pages']):
            data=self.request('GET',path,params)
            rows=data['orders']
            if not isinstance(rows,list):
                raise SafetyError('订单列表格式无效')
            for row in rows:
                result.setdefault(row['orderId'],row)
            if len(rows)<page_size:
                return list(result.values())
            oldest=min(int(r[time_field]) for r in rows)
            if oldest==last_bound:
                raise SafetyError('订单同微秒分页无法完整覆盖，停止交易，需核对历史')
            # Inclusive boundaries: repeat boundary and deduplicate, never skip it.
            params['to']=oldest
            last_bound=oldest
        raise SafetyError('订单分页达到配置上限，禁止将截断列表视为完整')

    def open_orders(self, symbol=None):
        return self._orders('/v1/openOrders','createdAt',symbol=symbol)

    def order_history(self, start=None, symbol=None):
        return self._orders('/v1/orders','updatedAt',start,symbol)

    def order(self, order_id):
        try:
            return self.request('GET','/v1/order/'+quote(str(order_id),safe=''),self.account_params())
        except ApiError as exc:
            if exc.status==404:
                return None  # NOT proof that a timed-out placement did not happen.
            raise

    def verify_leverage(self, market):
        leverage=(self.cfg['hedge_leverage'] if self.cfg.get('hedge_enabled') and market.get('marketDisplayName')==self.cfg['hedge_symbol'] else self.cfg['leverage'])
        fraction=dec(market['initialMarginFraction'])
        if market.get('isOutsideRth'):
            fraction=max(fraction,dec(market['offHoursInitialMarginFraction']))
        if fraction<=0 or dec(leverage)>1/fraction:
            raise SafetyError('配置杠杆超过市场当前上限')
        rows=self.request('GET','/v1/leverages',{**self.account_params(),'market':market.get('marketDisplayName',self.cfg['symbol'])})['leverages']
        matches=[x for x in rows if x['marketId']==market['marketId']]
        if len(matches)!=1 or dec(matches[0]['leverage'])!=dec(leverage) or matches[0]['marginMode']!='CROSS':
            raise SafetyError('真实杠杆/全仓模式与配置不一致，请在交易所设置并核对')

    def place(self, body, market):
        return self.request('POST','/v1/placeOrder',self.account_params(),body,
                            self.signed_headers(body['timestamp'],order_payload(body,market)))

    def cancel(self, record):
        ts=self.nonce()
        body={**self.account_params(),'marketId':record['body']['marketId'],'timestamp':ts}
        payload={'ad':self.address,'ai':self.account_index,'ct':ts,'m':body['marketId'],'op':2,'v':1}
        if record.get('order_id'):
            body.update(kind='orderId',orderId=record['order_id'])
            payload['id']=record['order_id']
        else:
            body.update(kind='clientId',clientId=record['body']['clientId'])
            payload['c']=body['clientId']
        return self.request('POST','/v1/cancelOrder',self.account_params(),body,self.signed_headers(ts,payload))

class OrderStream:
    """Public account order subscription. REST is used for reconciliation after reconnect."""
    def __init__(self, client):
        self.client = client
        self.lock = threading.Lock()
        self.orders = {}
        self.ready = set()
        self.last_message = 0.0
        self.stop_event = threading.Event()
        self.wake_event = threading.Event()
        self.app = None
        self.thread = None
        self.last_error = ""

    def start(self):
        import websocket
        def on_open(ws):
            with self.lock:
                self.ready.clear()
                self.orders.clear()
            for channel in ('orders', 'userFills'):
                ws.send(json.dumps({'type': 'subscribe', 'channel': channel,
                                     'id': self.client.address, 'accountIndex': self.client.account_index}))
        def on_message(ws, message):
            try:
                self.ingest(json.loads(message))
            except (ValueError, KeyError, TypeError):
                ws.close()
        def on_error(ws, error):
            self.last_error = type(error).__name__
        def on_pong(ws, data):
            self.last_message = time.monotonic()
            self.wake_event.set()
        def on_close(ws, *args):
            with self.lock:
                self.ready.clear()
        def run():
            while not self.stop_event.is_set():
                self.app = websocket.WebSocketApp(self.client.ws_url, on_open=on_open,
                    on_message=on_message, on_pong=on_pong, on_close=on_close, on_error=on_error)
                self.app.run_forever(ping_interval=self.client.cfg['ws_ping_sec'], ping_timeout=self.client.cfg['ws_ping_timeout_sec'], sslopt={'ca_certs': certifi.where()})
                self.stop_event.wait(self.client.cfg['ws_reconnect_sec'])
        self.thread = threading.Thread(target=run, daemon=True)
        self.thread.start()

    def ingest(self, frame):
        if frame.get('type') == 'error':
            self.last_error = '订单订阅返回错误'
            with self.lock:
                self.ready.clear()
            return
        if frame.get('type') not in ('subscribed', 'channel_data'):
            return
        channel = frame.get('channel')
        if channel not in ('orders', 'userFills'):
            return
        if str(frame.get('id', '')).lower() != self.client.address or frame.get('accountIndex', 0) != self.client.account_index:
            raise ValueError('subscription identity mismatch')
        contents = frame.get('contents')
        if not isinstance(contents, (dict, list)):
            raise ValueError('missing contents')
        with self.lock:
            self.last_message = time.monotonic()
            if frame['type'] == 'subscribed':
                self.ready.add(channel)
            if channel == 'orders':
                self._collect(contents)

    def _collect(self, value):
        if isinstance(value, dict):
            if 'orderId' in value and 'status' in value:
                oid = str(value['orderId'])
                old = self.orders.get(oid)
                if old and old.get('status') in TERMINAL and value.get('status') not in TERMINAL:
                    return
                if old and int(value.get('sequenceNumber', 0)) < int(old.get('sequenceNumber', 0)):
                    return
                self.orders[oid] = dict(value)
            else:
                for item in value.values():
                    self._collect(item)
        elif isinstance(value, list):
            for item in value:
                self._collect(item)

    def healthy(self):
        with self.lock:
            return self.ready == {'orders','userFills'} and time.monotonic()-self.last_message < self.client.cfg['ws_stale_sec']

    def find(self, client_id, order_id=None):
        with self.lock:
            rows = [dict(v) for v in self.orders.values() if (order_id and v.get('orderId') == order_id) or v.get('clientId') == client_id]
        return rows[-1] if rows else None

    def stop(self):
        self.stop_event.set()
        if self.app:
            self.app.close()

def filled_amount(order):
    original,remaining=dec(order['originalSize']),dec(order['remainingSize'])
    if original<=0 or not 0<=remaining<=original:
        raise SafetyError('订单成交量无效')
    filled=dec(order.get('filledSize',original-remaining))
    if filled!=original-remaining:
        raise SafetyError('filledSize和remainingSize不一致')
    return filled

def order_terminal(order):
    if order.get('cancelReason')=='MODIFY_CANCELED':
        raise SafetyError('发现外部改单操作，需核对后恢复')
    if order.get('status') in ('LIQUIDATED','ADL'):
        raise SafetyError('发现强平/ADL，不继续新增风险')
    state=order.get('state')
    return (order.get('status') in TERMINAL or state in ('FILLED','CANCELED','REJECTED')
            or (state=='PARTIALLY_FILLED' and order.get('timeInForce')=='IOC'))

def apply_order(record, order, client):
    body=record['body']
    if (order.get('clientId')!=body['clientId'] or order['marketId']!=body['marketId']
        or order['side']!=body['orderSide'] or dec(order['originalSize'])!=dec(body['quantity'])
        or bool(order.get('reduceOnly',False))!=body['reduceOnly']):
        raise SafetyError('订单回报与持久化意图不一致')
    if ('address' in order and order['address'].lower()!=client.address) or ('accountIndex' in order and int(order['accountIndex'])!=client.account_index):
        raise SafetyError('订单账户不匹配')
    fill=filled_amount(order)
    if fill<dec(record['filled']):
        raise SafetyError('订单成交量回退，等待同步')
    if order.get('status')=='FILLED' and fill!=dec(body['quantity']):
        raise SafetyError('FILLED状态与成交量不符')
    if fill>0 and dec(order.get('avgFillPrice',0))<=0:
        raise SafetyError('缺少真实成交均价')
    record.update(order_id=order['orderId'],status=order['status'],filled=str(fill),
                  avg_fill=str(order.get('avgFillPrice',0)),terminal=order_terminal(order),
                  sequence=int(order.get('sequenceNumber',0)),updated_at=int(order['updatedAt']))

def make_body(client, market, side, qty, price, tif, reduce, cid):
    if market['status']!='ONLINE':
        raise SafetyError('市场未开放')
    qty,price=dec(qty),dec(price)
    if qty<=0 or qty!=floor_step(qty,market['stepSize']) or qty>dec(market['maxOrderSize']):
        raise SafetyError('数量不符合交易所精度或上限')
    # Reduce-only dust semantics aren't guessed; API still enforces its own minima.
    if not reduce and (qty<dec(market['minOrderSize']) or qty*price<dec(market['minOrderNotional'])):
        raise SafetyError('金额/数量低于交易所最小值，不自动放大订单')
    ts=client.nonce()
    body={**client.account_params(),'marketId':market['marketId'],'orderSide':side,
          'orderType':'LIMIT','timeInForce':tif,'quantity':text_decimal(qty),'price':text_decimal(price),
          'goodTilTime':str(ts//1000+client.cfg['good_til_days']*86400*1000000),
          'timestamp':ts,'clientId':cid,'reduceOnly':reduce}
    order_payload(body,market)  # Exact tick/quantum conversion before journaling.
    return body

def opening_quantity(cfg, account, position, market, quote_data, price, amount):
    equity=dec(account['equity'])
    risk_price=max(dec(price),quote_data['ask'])
    if cfg['size_unit']=='equity_fraction':
        target=equity*dec(amount)
    elif cfg['size_unit']=='usd_notional':
        target=dec(amount)
    else:
        target=dec(amount)*risk_price
    existing=abs(dec(position.get('qty',0)))*risk_price
    others=sum(dec(p['notional']) for s,p in account['positions'].items() if s!=cfg['symbol'])
    available=min(equity*dec(cfg['max_symbol_equity_pct'])-existing,
                  equity*dec(cfg['max_account_equity_pct'])-others-existing,
                  equity*dec(cfg['max_margin_equity_pct'])*cfg['leverage']-others-existing,
                  (dec(account['free'])-dec(cfg['min_free_collateral_usd']))*cfg['leverage'])
    target=min(target,available)  # Retained legacy cap behavior.
    if target<=0:
        raise SafetyError('可用仓位预算不足')
    return floor_step(target/risk_price,market['stepSize'])

class OrderManager:
    def __init__(self, bot):
        self.bot=bot

    def active(self, roles=None):
        return [r for r in self.bot.state['orders'].values() if not r['terminal']
                and (roles is None or r['role'] in roles)]

    def submit(self, role, layer, side, qty, price, tif='ALO', reduce=False):
        b=self.bot
        if b.state.get('recovery_required'):
            raise SafetyError('账户/订单恢复尚未完成，禁止提交订单：'+b.state['recovery_required'])
        if b.cfg['dry_run']:
            log('DRY_RUN_ORDER',role=role,side=side,qty=qty,price=price,reduceOnly=reduce)
            return None
        if not b.stream.healthy():
            raise SafetyError('订单实时订阅不可用；禁止提交新订单')
        if role in ('E','G') and self.active({'E','G'}):
            raise SafetyError('已有首仓/补仓挂单或未知意图')
        if role in ('T','X') and self.active({'T','X'}):
            raise SafetyError('旧TP/平仓尚未确认撤销或成交')
        if role in ('E','G') and any(r['role']==role and r['layer']==layer for r in b.state['orders'].values()):
            raise SafetyError('该轮该层已有订单意图，禁止重复挂单')
        b.risk.verify_live_position_before_order()
        qty_now=dec(b.account['positions'].get(b.cfg['symbol'],{}).get('qty',0))
        if role=='E' and qty_now:
            raise SafetyError('真实BTC-USD仓位存在，禁止提交首仓E订单')
        if role=='G' and not qty_now:
            raise SafetyError('交易所真实BTC-USD仓位为零，禁止提交补仓订单')
        if self.active({'R'}):
            raise SafetyError('接管前残留订单尚未确认撤销，禁止新增订单')
        if reduce and (qty_now==0 or (side=='SELL')!=(qty_now>0) or dec(qty)>abs(qty_now)):
            raise SafetyError('reduce-only方向/数量与真实仓位不符')
        cid=f"{b.cfg['bot_prefix']}_{b.state['cycle']}_{role}{layer}_{uuid.uuid4().hex[:6]}"
        if len(cid)>36:
            raise SafetyError('clientId超过Arcus限制')
        body=make_body(b.client,b.market,side,qty,price,tif,reduce,cid)
        r=order_record(body,role,layer,b.client.now())
        b.state['orders'][cid]=r
        b.save()  # Write-ahead intent: even a crash before HTTP leaves a blocker.
        try:
            ack=b.client.place(body,b.market)
            if ack.get('clientId') not in (None,cid):
                raise UnknownOutcome('下单回执clientId不一致')
            r['order_id']=ack.get('orderId')
            r['status']='ACK_ONLY'
        except (UnknownOutcome,requests.RequestException):
            r['status']='OUTCOME_UNKNOWN'
            log('ORDER_UNKNOWN',clientId=cid,action='仅查询，不重发')
        b.save()
        if role=='T':
            terminal_trade_log('TP_SUBMITTED',交易对=b.cfg['symbol'],状态=r['status'],
                说明='提交结果，尚非成交确认',整仓均价=b.position().get('entry','0'),
                TP价格=body['price'],TP数量=body['quantity'],reduceOnly=body['reduceOnly'],订单ID=r['order_id'])
        return r

    def cancel(self, r):
        if r['terminal']:
            return
        b=self.bot
        if b.cfg['dry_run']:
            log('DRY_RUN_CANCEL',orderId=r['order_id'])
            return
        now=b.client.now()
        # Repeating cancellation is safe only for the same never-reused identity.
        if r['cancel_requested'] and now-r['cancel_time']<b.cfg['cancel_retry_sec']:
            return
        first_cancel = not r['cancel_requested']
        r.update(cancel_requested=True,cancel_time=now)
        b.save()
        try:
            b.client.cancel(r)
        except UnknownOutcome:
            log('CANCEL_UNKNOWN',clientId=r['body']['clientId'],action='等待订单终态')
        b.save()  # ACK is never proof of cancellation.
        if r['role']=='T' and first_cancel:
            terminal_trade_log('TP_CANCEL_REQUESTED',交易对=b.cfg['symbol'],旧TP价格=r['body']['price'],
                旧TP数量=r['body']['quantity'],订单ID=r['order_id'],说明='已请求撤单，等待交易所确认终态')

def parse_client_id(cid, prefix):
    m=re.fullmatch(re.escape(prefix)+r'_([0-9a-f]{14})_([EGHTX])(\d+)_([0-9a-f]{6})',str(cid))
    return (m[1],m[2],int(m[3])) if m else None

class RiskRecoveryManager:
    def adopt_position(self, account, candidate=None):
        b=self.bot
        pos=account['positions'].get(b.cfg['symbol'],{})
        qty=dec(pos.get('qty',0))
        if not qty or dec(pos['entry'])<=0:
            raise SafetyError('接管需要真实非零仓位和有效整仓均价')
        source=b.state if candidate is None else candidate
        remaining={}
        for cid,rec in source['orders'].items():
            if rec['terminal']:
                continue
            if rec['status'] in ('INTENT_SAVED','OUTCOME_UNKNOWN','ACK_ONLY'):
                raise SafetyError('订单状态尚未确认，不能重置为G0')
            rec=copy.deepcopy(rec)
            rec['baseline_filled']=rec['filled']
            if not rec['body']['reduceOnly']:
                rec['role']='R'  # Known old exposure: cancel, never count as new G1.
            elif (rec['body']['orderSide']=='SELL')!=(qty>0):
                rec['role']='X'  # D4 cancels wrong-side protection before replacement.
            remaining[cid]=rec
        cycle=f'{int(b.client.now()):08x}{uuid.uuid4().hex[:6]}'
        b.state=copy.deepcopy(source)
        b.state.update(cycle=cycle,orders=remaining,base_qty=str(qty),known_qty=str(qty),
                       sequence=account['sequence'],state='GRID_LONG' if qty>0 else 'GRID_SHORT',
                       exiting=False,exit_reason='',recovery_required='',
                       managed={'adopted_g0':{'qty':str(qty),'entry':pos['entry'],'time':b.client.now()},
                                'grid_layer':0,'layers':1,'last_fill_price':pos['entry'],
                                'position_entry':pos['entry']})
        b.account=account
        b.save()  # G0 is durable before any G1 or TP intent.
        b.emit('RECOVERY',state=b.state['state'],adopted='G0',qty=str(qty),anchor=pos['entry'])

    def import_protective_orders(self, rows, account):
        """Adopt only exchange-confirmed reduce-only LIMIT protection.

        Unregistered exposure orders remain blocked. No invented fill or E order.
        Historical partial fills are already included in the G0/account snapshot.
        """
        b=self.bot
        pos=account['positions'].get(b.cfg['symbol'],{})
        qty=dec(pos.get('qty',0))
        if not qty:
            return
        known_ids={r['order_id'] for r in b.state['orders'].values() if r['order_id']}
        changed=False
        for row in rows:
            if row['orderId'] in known_ids or row.get('clientId') in b.state['orders']:
                continue
            if row.get('reduceOnly') is not True:
                continue
            if row['marketId']!=b.market['marketId']:
                raise SafetyError('保护单市场不匹配')
            if row.get('orderType','LIMIT')!='LIMIT' or row.get('timeInForce') not in ('GTT','GTC','ALO'):
                raise SafetyError('已有保护单类型无法确认，禁止重复挂TP')
            body={**b.client.account_params(),'marketId':row['marketId'],'orderSide':row['side'],
                  'orderType':'LIMIT','timeInForce':'GTT' if row['timeInForce']=='GTC' else row['timeInForce'],
                  'quantity':row['originalSize'],'price':row['price'],'reduceOnly':True,
                  'clientId':row.get('clientId')}
            role='T' if (row['side']=='SELL')==(qty>0) else 'X'
            rec=order_record(body,role,0,row.get('createdAt',row['updatedAt'])/1e6)
            apply_order(rec,row,b.client)  # Includes market, side, account and fill checks.
            rec['baseline_filled']=rec['filled']
            key=row.get('clientId') or 'external:'+str(row['orderId'])
            b.state['orders'][key]=rec
            changed=True
        if changed:
            # D4's normal cancellation barrier handles multiple protection orders.
            closes=b.orders.active({'T','X'})
            if len(closes)>1:
                for rec in closes:
                    rec['role']='X'
            b.save()

    def require_confirmed_state(self):
        b = self.bot
        residual=b.orders.active({'R'})
        if residual:
            for rec in residual:
                b.orders.cancel(rec)
            raise SafetyError('接管前残留订单撤销中，等待交易所确认')
        if b.state.get('recovery_required'):
            raise SafetyError('账户/订单恢复尚未完成，保持监测且不下单：'+b.state['recovery_required'])

    def __init__(self, bot):
        self.bot = bot

    def recover(self):
        b = self.bot
        b.client.sync_time()
        b.market=b.client.market()
        # Startup always reads real account + open orders + individual order states.
        b.account=b.client.account()
        open_rows=b.client.open_orders()
        if not b.had_state and b.position():
            self.adopt_position(b.account)
            b.had_state=True
        if not b.had_state:
            history=b.client.order_history()
            own=[r for r in history if parse_client_id(r.get('clientId',''),b.cfg['bot_prefix'])]
            own += [r for r in open_rows if parse_client_id(r.get('clientId',''),b.cfg['bot_prefix'])
                    and r['orderId'] not in {x['orderId'] for x in own}]
            if own:
                latest=max(own,key=lambda r:int(r.get('createdAt',r['updatedAt'])))
                cycle=parse_client_id(latest['clientId'],b.cfg['bot_prefix'])[0]
                cycles={parse_client_id(r['clientId'],b.cfg['bot_prefix'])[0] for r in open_rows
                        if parse_client_id(r.get('clientId',''),b.cfg['bot_prefix'])}
                if len(cycles)>1 or (cycles and cycle not in cycles):
                    raise SafetyError('多轮机器人挂单并存，需要核对归属')
                b.state['cycle']=cycle
                bar=int(cycle[:8],16)
                entry=next((r for r in own if parse_client_id(r['clientId'],b.cfg['bot_prefix'])[:2]==(cycle,'E')),None)
                if entry:
                    b.state['ledger']=dict(last_signal_bar=bar,last_signal_side='LONG' if entry['side']=='BUY' else 'SHORT',signal_time=entry['createdAt']/1e6)
                for row in own:
                    parsed=parse_client_id(row['clientId'],b.cfg['bot_prefix'])
                    if parsed[0]!=cycle:
                        continue
                    _,role,layer=parsed
                    tif=row.get('timeInForce','GTT')
                    body={**b.client.account_params(),'marketId':row['marketId'],'orderSide':row['side'],
                          'orderType':'LIMIT','timeInForce':'GTT' if tif=='GTC' else tif,
                          'quantity':row['originalSize'],'price':row['price'],
                          'reduceOnly':bool(row.get('reduceOnly',False)),'clientId':row['clientId']}
                    rec=order_record(body,role,layer,row.get('createdAt',row['updatedAt'])/1e6)
                    apply_order(rec,row,b.client)
                    b.state['orders'][row['clientId']]=rec
                expected=b.expected_qty(b.state)
                actual=dec(b.position().get('qty',0))
                if expected!=actual:
                    b.state['base_qty']=str(actual-expected)
                    b.state.update(exiting=True,exit_reason='外部真实平仓',recovery_required='')
                b.state['known_qty']=str(actual)
                b.rebuild_managed()
            elif b.position():
                self.adopt_position(b.account)
            b.state['sequence']=b.account['sequence']
            b.save()
        b.reconcile()
        b.set_position_state()
        b.save()
        b.emit('RECOVERY',state=b.state['state'],qty=b.position().get('qty','0'),
                  orders=len(b.orders.active()),issue=b.state['recovery_required'])


    @staticmethod
    def expected_qty(state):
        return dec(state['base_qty'])+sum((dec(r['filled'])-dec(r.get('baseline_filled',0)))*(1 if r['body']['orderSide']=='BUY' else -1)
                                         for r in state['orders'].values())


    def rebuild_managed(self):
        b = self.bot
        records=[r for r in b.state['orders'].values() if r['role'] in ('E','G') and dec(r['filled'])>0]
        if records:
            newest=max(records,key=lambda r:(r['updated_at'],r['layer']))
            b.state['managed'].update(layers=len({r['layer'] for r in records}),
                last_fill_price=newest['avg_fill'],last_trade_time=newest['updated_at']/1e6,
                last_entry_bar=b.state['ledger'].get('last_signal_bar'))
        full=[r['layer'] for r in records if r['terminal'] and dec(r['filled'])==dec(r['body']['quantity'])]
        b.state['managed']['grid_layer']=max(full,default=0)
        if b.state['managed'].get('adopted_g0'):
            b.state['managed']['layers']=b.state['managed']['grid_layer']+1


    def reconcile(self):
        b = self.bot
        open_rows=b.client.open_orders()
        snapshot=b.client.account()
        if not b.state['cycle'] and dec(snapshot['positions'].get(b.cfg['symbol'],{}).get('qty',0)):
            self.adopt_position(snapshot)
        self.import_protective_orders(open_rows,snapshot)
        known=set(b.state['orders'])
        known_ids={r['order_id'] for r in b.state['orders'].values() if r['order_id']}
        foreign=[r for r in open_rows if r.get('clientId') not in known and r['orderId'] not in known_ids]
        if foreign:
            raise SafetyError('当前市场存在未登记挂单；不能盲目接管或重复挂单')
        candidate=copy.deepcopy(b.state)
        history=None
        unknown=[]
        changed_entry=False
        any_close_fill=False
        for cid,rec in candidate['orders'].items():
            if rec['terminal']:
                continue
            observed=[]
            if b.stream:
                event=b.stream.find(cid,rec['order_id'])
                if event:
                    observed.append(event)
            if rec['order_id']:
                row=b.client.order(rec['order_id'])
                if row:
                    observed.append(row)
            observed += [r for r in open_rows if r['orderId']==rec['order_id'] or (rec['body']['clientId'] is not None and r.get('clientId')==rec['body']['clientId'])]
            if not observed:
                if history is None:
                    start=min(int(r['created_at']*1e6) for r in candidate['orders'].values())
                    history=b.client.order_history(start)
                observed=[r for r in history if r['orderId']==rec['order_id'] or (rec['body']['clientId'] is not None and r.get('clientId')==rec['body']['clientId'])]
            if not observed:
                unknown.append(cid)
                continue
            row=max(observed,key=lambda r:(int(r.get('sequenceNumber',0)),int(r.get('updatedAt',0)),filled_amount(r)))
            before=dec(rec['filled'])
            apply_order(rec,row,b.client)
            changed_entry |= rec['role'] in ('E','G') and dec(rec['filled'])>before
            any_close_fill |= rec['role'] in ('T','X') and dec(rec['filled'])>before
        account=b.client.account()  # After fetching order lifecycle, never reuse pre-fill average.
        if account['sequence']<b.state['sequence']:
            raise SafetyError('账户快照回退')
        actual=dec(account['positions'].get(b.cfg['symbol'],{}).get('qty',0))
        max_seq=max((r['sequence'] for r in candidate['orders'].values()),default=0)
        expected=b.expected_qty(candidate)
        if account['sequence']<max_seq:
            raise SafetyError('等待订单成交数量与真实持仓同步；禁止继续下单')
        pos=account['positions'].get(b.cfg['symbol'],{})
        previous_entry=candidate['managed'].get('position_entry')
        entry_changed=(actual and previous_entry is not None and dec(pos['entry'])!=dec(previous_entry))
        untracked=(actual and (candidate.get('recovery_required') or
                   (not candidate['managed'].get('adopted_g0')
                    and not any(r['role']=='E' and dec(r['filled'])>0 for r in candidate['orders'].values()))))
        if actual!=expected or (entry_changed and not changed_entry and not any_close_fill) or untracked:
            # A changing known fill / unknown intent remains an accounting barrier,
            # never evidence of a new external position.
            if unknown or changed_entry or any_close_fill:
                raise SafetyError('等待订单成交数量与真实持仓同步；禁止继续下单')
            if actual:
                self.adopt_position(account,candidate)
                b.set_position_state()
                b.save()
                return True
            if expected:
                # Manual/external close: retain order journal for safe cancellation.
                candidate['base_qty']=str(dec(candidate['base_qty'])-expected)
                candidate.update(exiting=True,exit_reason='外部真实平仓')
        candidate.update(known_qty=str(actual),sequence=account['sequence'])
        if actual:
            candidate['managed']['position_entry']=pos['entry']
        if changed_entry:
            candidate['managed'].update(peak_pnl=0,tp_armed=False)
        if any_close_fill:
            candidate['exiting']=True
            candidate['exit_reason']=candidate['exit_reason'] or '止盈/平仓已有真实成交，结束本轮'
        b.account=account
        b.state=candidate
        b.rebuild_managed()
        b.set_position_state()
        b.save()
        if unknown:
            raise SafetyError('未确认订单意图仍存在；超时/404不是未下单证明：'+','.join(unknown))
        return True


    def verify_live_position_before_order(self):
        """Independent REST read immediately before journaling any new order.

        If a manual trade occurred since reconciliation, abort this placement.
        The next normal reconciliation must establish the new state and prices;
        neither the local journal nor the earlier in-memory snapshot can replace
        a fresh exchange position. Read failures never fall back to cached data.
        """
        b=self.bot
        fresh=b.client.account()
        if fresh['sequence']<max(b.account['sequence'],b.state['sequence']):
            raise SafetyError('下单前交易所账户快照回退，禁止提交订单')
        old=b.account['positions'].get(b.cfg['symbol'],{})
        live=fresh['positions'].get(b.cfg['symbol'],{})
        old_qty,live_qty=dec(old.get('qty',0)),dec(live.get('qty',0))
        if (old_qty!=live_qty or (live_qty and dec(old['entry'])!=dec(live['entry']))):
            raise SafetyError('下单前交易所真实仓位数量/均价已变化，本次不下单，等待重新对账')
        b.account=fresh

    def daily_halt_blocks_management(self):
        """Daily halt still blocks new entry cycles (D2 checks the raw flag).

        An adopted real G0 continues its existing grid/TP/SL management even
        when the account's daily flag is halted. Do not clear/reset daily loss
        accounting. Price stop-loss and all other risk checks stay in force.
        The exception ends with the adopted cycle's real position.
        """
        b=self.bot
        adopted_position=(b.state['managed'].get('adopted_g0')
                          and dec(b.position().get('qty',0))!=0)
        return bool(b.state['daily'].get('halted')) and not bool(adopted_position)

    def check_open_risk(self,q):
        b = self.bot
        if b.state['recovery_required'] or self.daily_halt_blocks_management():
            raise SafetyError('恢复/日内风控禁止新增风险')
        if (q['ask']-q['bid'])/q['mid']*10000>dec(b.cfg['max_spread_bps']):
            raise SafetyError('价差超过上限')
        b.client.verify_leverage(b.market)


    def update_daily(self):
        b = self.bot
        day=datetime.fromtimestamp(b.client.now(),timezone.utc).date().isoformat()
        a=b.account
        equity,deposits=dec(a['equity']),dec(a['deposits'])
        d=b.state['daily']
        if d.get('day')!=day:
            d={'day':day,'start_equity':str(equity),'start_deposits':str(deposits),'peak':str(equity),'halted':False}
        adjusted=equity-(deposits-dec(d['start_deposits']))
        peak=max(dec(d['peak']),adjusted)
        d['peak']=str(peak)
        if (dec(d['start_equity'])-adjusted>=dec(b.cfg['max_daily_loss_usd']) or
            (peak>0 and (peak-adjusted)/peak>=dec(b.cfg['max_daily_drawdown_pct']))):
            d['halted']=True
        b.state['daily']=d
        b.save()



# ============================================================
# BTC + ETH paired cycle. Legacy grid implementation stays available separately.
# ============================================================
PAIR = ('BTC-USD', 'ETH-USD')

def evaluate_hedge(five, cfg, *, ledger=None, account_known=False,
                   position_side='', has_entry_order=False, current_price=None, now=None):
    now=time.time() if now is None else now
    ledger={} if ledger is None else ledger
    r=dict(signal=False,side='',state='WAIT',grid_state=None,price=current_price,
           rsi_5m=None,long_signal=False,short_signal=False,bar_5m=None,bar=None,reason='')
    try:
        f=closed_rows(five,300,cfg['rsi_period']+1,now)
        a=calc_rsi([x['close'] for x in f],cfg['rsi_period'])
        long_signal=a<cfg['rsi_long_threshold']
        short_signal=a>cfg['rsi_short_threshold']
        side='LONG' if long_signal else 'SHORT' if short_signal else ''
        r.update(rsi_5m=a,long_signal=long_signal,short_signal=short_signal,
                 bar_5m=f[-1]['time'],bar=f[-1]['time'])
        if not account_known:
            r['reason']='BTC/ETH持仓和挂单尚未确认'
        elif position_side or has_entry_order:
            r['reason']='本轮尚未结束，不创建新首仓'
        elif not side:
            r['reason']='5M RSI位于45至55中性区间'
        elif signal_seen(ledger,r['bar_5m']):
            r['reason']='本根5M K线已使用或时间回退'
        else:
            ledger.update(last_signal_bar=r['bar'],last_signal_bar_5m=r['bar_5m'],
                          last_signal_side=side,signal_time=now)
            r.update(signal=True,side=side,state=side+'_ORDER_PENDING',reason='BTC已收盘5M RSI12状态满足')
    except (ValueError,TypeError,KeyError,OverflowError) as exc:
        r['reason']='数据不可用：'+str(exc)
    return r

class PairNotifications(TelegramNotifications):
    def baseline(self):
        self.ready=True

    def startup(self, state=None):
        if self.started:
            return
        self.started=True
        self._enqueue(f'Arcus双币种对冲机器人启动\n交易对：BTC对冲ETH\n时间：{self._time()}')

    def event(self,key,message):
        self._claim_and_enqueue(str(self.bot.state['cycle'])+':'+key,message)

class HedgeBot(BotState):
    """Write-ahead, two-market state machine; an ACK never counts as a hedge/fill."""
    def __init__(self,cfg,client,stream,path,emit=log):
        super().__init__(cfg,client,stream,path,emit)
        self.markets={}
        self.notifications=PairNotifications(self)
        self.risk=RiskRecoveryManager(self)  # Preserve the existing daily-loss accounting.
        self.grid=GridManager(self)

    def active(self,symbol=None,roles=None):
        return [r for r in self.state['orders'].values() if not r['terminal']
                and (symbol is None or r['symbol']==symbol)
                and (roles is None or r['role'] in roles)]

    def pos(self,symbol):
        return self.account['positions'].get(symbol,{})

    def qty(self,symbol):
        return dec(self.pos(symbol).get('qty',0))

    def event(self,key,message):
        self.notifications.safe('event',key,message)

    def expected(self,symbol,state=None):
        s=self.state if state is None else state
        return dec(s['pair']['base_qty'][symbol])+sum(
            (dec(r['filled'])-dec(r.get('baseline_filled',0)))*(1 if r['body']['orderSide']=='BUY' else -1)
            for r in s['orders'].values() if r['symbol']==symbol)

    def notionals(self):
        p=self.state['pair']
        btc=dec(p['base_btc_notional'])
        eth=dec(p['base_eth_notional'])
        for r in self.state['orders'].values():
            value=dec(r['filled'])*dec(r['avg_fill'])-dec(r.get('baseline_notional',0))
            if r['role']=='E' and r['symbol']==PAIR[0]: btc+=value
            if r['role']=='H' and r['symbol']==PAIR[1]: eth+=value
        return btc,eth

    def import_row(self,row):
        parsed=parse_client_id(row.get('clientId',''),self.cfg['bot_prefix'])
        if not parsed or (self.state['cycle'] and parsed[0]!=self.state['cycle']):
            raise SafetyError('BTC/ETH存在非本轮挂单，需核对归属')
        symbol=next((s for s,m in self.markets.items() if m['marketId']==row['marketId']),None)
        if symbol is None: raise SafetyError('本轮订单市场不匹配')
        if not self.state['cycle']: self.state['cycle']=parsed[0]
        tif=row.get('timeInForce','GTT')
        body={**self.client.account_params(),'marketId':row['marketId'],'orderSide':row['side'],
              'orderType':row.get('orderType','LIMIT'),'timeInForce':'GTT' if tif=='GTC' else tif,
              'quantity':row['originalSize'],'price':row['price'],
              'reduceOnly':bool(row.get('reduceOnly',False)),'clientId':row['clientId']}
        rec=order_record(body,parsed[1],parsed[2],int(row.get('createdAt',row['updatedAt']))/1e6)
        rec['symbol']=symbol
        apply_order(rec,row,self.client)
        self.state['orders'][row['clientId']]=rec

    def adopt_positions(self):
        """Rebase on confirmed exchange inventory, never on a cached/local price.

        Called only after order reconciliation; preserve daily risk, ledger, cooldown,
        and the entire order journal. Existing filled records become the baseline.
        """
        if self.state['exiting']:
            raise SafetyError('EXITING周期禁止重新接管为开仓管理')
        if self.active(roles={'E','H','G','X'}):
            raise SafetyError('开仓/平仓订单尚未结束，禁止重建接管基线')
        snapshot=self.account
        fresh=self.client.account()
        if fresh['sequence']<max(snapshot['sequence'],self.state['sequence']):
            raise SafetyError('接管时交易所账户快照回退')
        for symbol in PAIR:
            old=snapshot['positions'].get(symbol,{})
            pos=fresh['positions'].get(symbol,{})
            qty=dec(pos.get('qty',0))
            if qty!=dec(old.get('qty',0)) or (qty and dec(pos['entry'])!=dec(old['entry'])):
                raise SafetyError('接管时真实仓位数量/均价变化，等待下一次对账')
            if qty and dec(pos.get('entry',0))<=0:
                raise SafetyError('接管仓位缺少有效真实开仓均价')
        self.account=fresh
        btc,eth=self.qty(PAIR[0]),self.qty(PAIR[1])
        if not btc and not eth:
            raise SafetyError('没有真实BTC/ETH仓位可接管')
        if not self.state['cycle']:
            self.state['cycle']=f'{int(self.client.now()):08x}'+uuid.uuid4().hex[:6]
        btc_value=abs(btc)*dec(self.pos(PAIR[0]).get('entry',0))
        eth_value=abs(eth)*dec(self.pos(PAIR[1]).get('entry',0))
        self.state['pair'].update(
            base_qty={symbol:str(self.qty(symbol)) for symbol in PAIR},
            base_btc_notional=str(btc_value),base_eth_notional=str(eth_value),
            btc_filled_notional=str(btc_value),hedged_btc_notional=str(eth_value),
            residual_notional=str(btc_value-eth_value),
            position_entries={symbol:str(self.pos(symbol).get('entry',0)) for symbol in PAIR})
        for rec in self.state['orders'].values():
            rec['baseline_filled']=rec['filled']
            rec['baseline_notional']=str(dec(rec['filled'])*dec(rec['avg_fill']))
        self.state['sequence']=fresh['sequence']
        self.state['state']='GRID_LONG' if btc>0 else 'GRID_SHORT'
        self.save()
        self.emit('ADOPTED',BTC数量=str(btc),BTC真实均价=self.pos(PAIR[0]).get('entry','0'),
                  ETH数量=str(eth),ETH真实均价=self.pos(PAIR[1]).get('entry','0'))
        if eth and (not btc or btc*eth>0):
            self.begin_exit('接管时双腿方向或仓位异常')

    def recover(self):
        self.markets={s:self.client.market(s) for s in PAIR}
        self.market=self.markets[PAIR[0]]
        self.account=self.client.account()
        opens=[r for s in PAIR for r in self.client.open_orders(s)]
        if 'pair' not in self.state:
            # Upgrade old journals without losing uncertain intents or outstanding orders.
            for r in self.state['orders'].values():
                r['symbol']=next((s for s,m in self.markets.items() if m['marketId']==r['body']['marketId']),None)
                if r['symbol'] is None: raise SafetyError('旧订单不属于BTC/ETH市场')
                if not r['terminal']:
                    rows=[x for x in opens if x.get('clientId')==r['body']['clientId']]
                    row=self.client.order(r['order_id']) if r['order_id'] else None
                    if row: rows.append(row)
                    if not rows:
                        rows=[x for x in self.client.order_history(int(r['created_at']*1e6),r['symbol'])
                              if x.get('clientId')==r['body']['clientId']]
                    if not rows: raise SafetyError('旧订单意图未确认，禁止迁移并重复开仓')
                    apply_order(r,max(rows,key=lambda x:int(x['updatedAt'])),self.client)
            if not self.had_state:
                history=[r for s in PAIR for r in self.client.order_history(symbol=s)
                         if parse_client_id(r.get('clientId',''),self.cfg['bot_prefix'])]
                own_open=[r for r in opens if parse_client_id(r.get('clientId',''),self.cfg['bot_prefix'])]
                candidates=own_open or history
                if candidates:
                    latest=max(candidates,key=lambda r:int(r.get('createdAt',r['updatedAt'])))
                    self.state['cycle']=parse_client_id(latest['clientId'],self.cfg['bot_prefix'])[0]
                    for row in history:
                        if parse_client_id(row['clientId'],self.cfg['bot_prefix'])[0]==self.state['cycle']:
                            self.import_row(row)
            for row in opens:
                if row.get('clientId') not in self.state['orders']: self.import_row(row)
            self.account=self.client.account()
            if self.account['sequence']<max([self.state['sequence']]+[r['sequence'] for r in self.state['orders'].values()]):
                raise SafetyError('迁移时账户与订单尚未同步')
            btc,eth=self.qty(PAIR[0]),self.qty(PAIR[1])
            if (btc or eth) and not self.state['cycle']:
                self.state['cycle']=f'{int(self.client.now()):08x}'+uuid.uuid4().hex[:6]
            self.state['pair']={'version':1,'base_qty':{s:str(self.qty(s)) for s in PAIR},
                'base_btc_notional':str(abs(btc)*dec(self.pos(PAIR[0]).get('entry',0))),
                'base_eth_notional':str(abs(eth)*dec(self.pos(PAIR[1]).get('entry',0))),
                'hedged_btc_notional':'0','btc_filled_notional':'0','residual_notional':'0'}
            for r in self.state['orders'].values():
                r['baseline_filled']=r['filled']
                r['baseline_notional']=str(dec(r['filled'])*dec(r['avg_fill']))
            if eth and (not btc or btc*eth>0):
                self.state.update(exiting=True,exit_reason='恢复时双腿方向或仓位异常')
            if any(r['role'] in ('T','X') and dec(r['filled'])>0 for r in self.state['orders'].values()):
                self.state.update(exiting=True,exit_reason='恢复发现本轮已有平仓成交')
            self.state['sequence']=self.account['sequence']
            self.save()
        pair=self.state['pair']
        if pair.get('version')!=1 or set(pair.get('base_qty',{}))!=set(PAIR):
            raise SafetyError('双币种持久化状态格式无效')
        for key in ('base_btc_notional','base_eth_notional'):
            if dec(pair[key])<0: raise SafetyError('双币种持久化名义金额无效')
        for symbol in PAIR: dec(pair['base_qty'][symbol])
        self.reconcile()
        self.notifications.safe('baseline')
        self.emit('RECOVERY',state=self.state['state'],positions={s:str(self.qty(s)) for s in PAIR})

    def begin_exit(self,reason):
        if not self.state['cycle']: return
        self.state.update(exiting=True,state='EXITING',exit_reason=self.state['exit_reason'] or reason)
        self.save()  # Persist the irreversible cycle gate BEFORE any cancellations/HTTP.
        if self.state['exit_reason'] not in ('外部真实仓位变化','首仓未成交或外部平仓'):
            self.event('flatten','FLATTEN_ALL开始\n原因：'+self.state['exit_reason'])

    def reconcile(self):
        opens=[r for s in PAIR for r in self.client.open_orders(s)]
        candidate=copy.deepcopy(self.state)
        unknown=[]
        events=[]
        for cid,r in candidate['orders'].items():
            if r['terminal']: continue
            rows=[x for x in opens if x.get('clientId')==cid or x['orderId']==r['order_id']]
            event=self.stream.find(cid,r['order_id']) if self.stream else None
            if event: rows.append(event)
            row=self.client.order(r['order_id']) if r['order_id'] else None
            if row: rows.append(row)
            if not rows:
                rows=[x for x in self.client.order_history(int(r['created_at']*1e6),r['symbol'])
                      if x.get('clientId')==cid or x['orderId']==r['order_id']]
            if not rows:
                unknown.append(cid)
                continue
            before=dec(r['filled'])
            apply_order(r,max(rows,key=lambda x:(int(x.get('sequenceNumber',0)),int(x['updatedAt']),filled_amount(x))),self.client)
            if dec(r['filled'])>before:
                events.append((cid,r))
                if r['role'] in ('T','X','G'):
                    candidate.update(exiting=True,state='EXITING',exit_reason=candidate['exit_reason'] or (r['symbol']+' TP/平仓真实成交' if r['role']!='G' else '旧补仓订单发生真实成交'))
        # Save observed TP fills immediately, even if a later account read fails.
        self.state=candidate
        self.save()
        if self.state['exiting']: self.begin_exit(self.state['exit_reason'])
        account=self.client.account()
        if account['sequence']<max([self.state['sequence']]+[r['sequence'] for r in candidate['orders'].values()]):
            raise SafetyError('双币种账户与订单尚未同步，禁止新增订单')
        known_ids={r['order_id'] for r in candidate['orders'].values() if r['order_id']}
        foreign=[r for r in opens if r.get('clientId') not in candidate['orders'] and r['orderId'] not in known_ids]
        self.account=account
        if foreign: raise SafetyError('BTC/ETH存在未登记挂单，禁止新开仓或结束本轮')
        if unknown:
            if self.state['exiting']:
                # Cancellation by the original clientId is safe; replacing the intent is not.
                for cid in unknown: self.cancel(self.state['orders'][cid])
            raise SafetyError('订单结果未确认，仅查询、不重发：'+','.join(unknown))
        mismatches=[symbol for symbol in PAIR if self.qty(symbol)!=self.expected(symbol)]
        entries=candidate['pair'].get('position_entries',{})
        entry_changed=any(self.qty(symbol) and symbol in entries
                          and dec(self.pos(symbol)['entry'])!=dec(entries[symbol]) for symbol in PAIR)
        # On upgrade/restart, also detect a changed average without relying on a
        # previously stored price snapshot. Current real entry value is authoritative.
        expected_values=self.notionals()
        value_changed=any(self.qty(symbol) and abs(self.qty(symbol))*dec(self.pos(symbol)['entry'])!=value
                          for symbol,value in zip(PAIR,expected_values))
        changed_exposure=any(r['role'] in ('E','H') for _,r in events)
        need_adopt=(not self.state['cycle'] and any(self.qty(symbol) for symbol in PAIR))
        need_adopt |= bool(mismatches) or ((entry_changed or value_changed) and not events)
        if need_adopt:
            if self.active(roles={'E','H'}) or changed_exposure:
                if mismatches:
                    raise SafetyError('等待双腿成交回报与真实仓位数量同步')
                # Known partial fills retain their cumulative fill accounting.
            elif self.state['exiting'] or any(self.expected(symbol) and not self.qty(symbol) for symbol in PAIR):
                # Manual closing of a leg and all prior exit gates still end the cycle.
                if not self.state['cycle']:
                    raise SafetyError('无周期的本地仓位基线与交易所不符，需核对状态')
                self.begin_exit(self.state['exit_reason'] or '外部真实仓位变化')
                for symbol in mismatches:
                    delta=self.qty(symbol)-self.expected(symbol)
                    candidate['pair']['base_qty'][symbol]=str(dec(candidate['pair']['base_qty'][symbol])+delta)
            elif any(self.qty(symbol) for symbol in PAIR):
                self.adopt_positions()
        self.state['sequence']=self.account['sequence']
        self.state['pair']['position_entries']={symbol:str(self.pos(symbol).get('entry',0)) for symbol in PAIR}
        if all(self.qty(symbol) for symbol in PAIR):
            self.state['pair'].setdefault('opened_at', self.client.now())
        btc,eth=self.notionals()
        self.state['pair'].update(btc_filled_notional=str(btc),hedged_btc_notional=str(eth),residual_notional=str(btc-eth))
        if self.state['exiting']:
            self.state['state']='EXITING'
        elif self.state['cycle']:
            self.state['state']='GRID_LONG' if self.qty(PAIR[0])>0 else 'GRID_SHORT' if self.qty(PAIR[0])<0 else ('LONG_ORDER_PENDING' if self.active(PAIR[0],{'E'}) and self.active(PAIR[0],{'E'})[0]['body']['orderSide']=='BUY' else 'SHORT_ORDER_PENDING')
        else: self.state['state']='WAIT'
        self.save()
        for cid,r in events:
            if r['role'] in ('E','H'):
                label='BTC首仓真实成交' if r['role']=='E' else 'ETH反向仓建立成功'
                direction='LONG' if r['body']['orderSide']=='BUY' else 'SHORT'
                self.event(cid+':'+r['filled'],f"{label}\n方向：{direction}\n累计实际成交qty：{r['filled']}\n累计实际成交美元名义价值：{dec(r['filled'])*dec(r['avg_fill'])}")
            elif r['role']=='T':
                self.event(cid+':tp',r['symbol']+' TP成交\n本轮进入FLATTEN_ALL')
        return opens

    def submit(self,symbol,role,side,qty,price,tif='GTT',reduce=False,market_order=False):
        if role=='G': raise SafetyError('双币种模式禁止所有G订单')
        before={s:(self.qty(s),self.pos(s).get('entry')) for s in PAIR}
        self.reconcile()  # Includes both TP fills immediately before every new intent.
        if before!={s:(self.qty(s),self.pos(s).get('entry')) for s in PAIR}:
            raise SafetyError('下单前真实仓位变化，重新计算订单')
        if self.state['exiting'] and role!='X': return None
        if not self.state['cycle']: raise SafetyError('无cycle，不允许提交订单')
        if role=='E' and (any(self.qty(s) for s in PAIR) or self.active()):
            raise SafetyError('双腿未归零或仍有挂单，禁止BTC首仓')
        if role=='H' and self.active(PAIR[1],{'H'}): return None
        if role=='X' and self.active(symbol,{'T','X'}): return None
        if role=='T' and self.active(symbol,{'X'}): return None
        if role=='X' and self.active(roles={'E','H','G','T'}): return None
        real=self.qty(symbol)
        if reduce and (not real or (side=='SELL')!=(real>0) or dec(qty)>abs(real)):
            raise SafetyError('双腿平仓方向/数量与真实仓位不符')
        if not self.stream.healthy(): raise SafetyError('订单实时订阅不可用，禁止提交订单')
        if self.cfg['dry_run']: raise SafetyError('观察模式禁止提交订单')
        cid=f"{self.cfg['bot_prefix']}_{self.state['cycle']}_{role}{0 if symbol==PAIR[0] else 1}_{uuid.uuid4().hex[:6]}"
        body=make_body(self.client,self.markets[symbol],side,qty,price,tif,reduce,cid)
        if market_order:
            if tif!='IOC': raise SafetyError('MARKET必须使用IOC')
            body['orderType']='MARKET'
        rec=order_record(body,role,0 if symbol==PAIR[0] else 1,self.client.now())
        rec['symbol']=symbol
        self.state['orders'][cid]=rec
        self.save()
        try:
            ack=self.client.place(body,self.markets[symbol])
            if ack.get('clientId') not in (None,cid): raise UnknownOutcome('clientId回执不一致')
            rec.update(order_id=ack.get('orderId'),status='ACK_ONLY')
        except (UnknownOutcome,requests.RequestException):
            rec['status']='OUTCOME_UNKNOWN'
        self.save()
        return rec

    def cancel(self,rec):
        if rec['terminal']: return
        now=self.client.now()
        if rec['cancel_requested'] and now-rec['cancel_time']<self.cfg['cancel_retry_sec']: return
        rec.update(cancel_requested=True,cancel_time=now)
        self.save()
        try: self.client.cancel(rec)
        except UnknownOutcome: pass
        self.save()

    def check_budget(self,symbol,notional,pair_reserve=False):
        a=self.account; equity=dec(a['equity']); n=dec(notional)
        existing=sum(abs(dec(p['notional'])) for p in a['positions'].values())
        own=abs(dec(self.pos(symbol).get('notional',0)))
        # Pending BTC first-entry remainder also consumes future paired exposure.
        reserved=sum((dec(r['body']['quantity'])-dec(r['filled']))*dec(r['body']['price'])
                     for r in self.active(roles={'E'}))
        required=n*2 if pair_reserve else n+reserved*2
        leverage={PAIR[0]:dec(self.cfg['leverage']),PAIR[1]:dec(self.cfg['hedge_leverage'])}
        existing_margin=sum(abs(dec(p['notional']))/leverage.get(s,dec(self.cfg['leverage']))
                            for s,p in a['positions'].items())
        paired_margin=1/leverage[PAIR[0]]+1/leverage[PAIR[1]]
        required_margin=n*paired_margin if pair_reserve else n/leverage[symbol]+reserved*paired_margin
        if (own+n>equity*dec(self.cfg['max_symbol_equity_pct'])
            or existing+required>equity*dec(self.cfg['max_account_equity_pct'])
            or existing_margin+required_margin>equity*dec(self.cfg['max_margin_equity_pct'])
            or required_margin>dec(a['free'])-dec(self.cfg['min_free_collateral_usd'])):
            raise SafetyError('BTC+ETH美元名义金额超过现有风险/保证金上限')

    def hedge_tick(self):
        if self.state['exiting'] or not self.qty(PAIR[0]) or self.active(PAIR[1],{'H'}): return
        btc,covered=self.notionals()
        missing=btc-covered
        if missing<=0: return
        symbol=PAIR[1]; market=self.markets[symbol]; q=self.client.quote(symbol)
        side='SELL' if self.qty(PAIR[0])>0 else 'BUY'
        executable=q['bid'] if side=='SELL' else q['ask']
        qty=floor_step(min(missing/executable,dec(market['maxOrderSize'])),market['stepSize'])
        if qty<dec(market['minOrderSize']) or qty*executable<dec(market['minOrderNotional']): return
        self.client.verify_leverage(market)
        self.check_budget(symbol,qty*executable)
        self.submit(symbol,'H',side,qty,exit_limit(q,side,self.cfg,market),'IOC',False,True)

    def pair_pnl(self):
        """Return net USD PnL and return for both live legs."""
        total_pnl=Decimal('0'); total_notional=Decimal('0'); live=0
        for symbol in PAIR:
            pos=self.pos(symbol); qty=dec(pos.get('qty',0)); entry=dec(pos.get('entry',0))
            if not qty or entry <= 0: continue
            q=self.client.quote(symbol)
            if qty > 0: pnl=qty*(dec(q['bid'])-entry)
            else: pnl=abs(qty)*(entry-dec(q['ask']))
            total_pnl += pnl; total_notional += abs(qty)*entry; live += 1
        if live != len(PAIR) or total_notional <= 0: return Decimal('0'), None
        fee=total_notional*dec(self.cfg.get('fee_buffer_bps',0))/Decimal('10000')
        net=total_pnl-fee
        return net, net/total_notional

    def pair_risk_trigger(self):
        if not all(self.qty(symbol) for symbol in PAIR): return None
        net, ret=self.pair_pnl()
        if ret is None: return None
        tp=dec(self.cfg.get('pair_take_profit_pct','0.005'))
        sl=dec(self.cfg.get('pair_stop_loss_pct','0.007'))
        if ret >= tp: return f'组合净利润达到止盈目标：{ret:.4%}，约{net:.2f} USD'
        if ret <= -sl: return f'组合净亏损达到止损目标：{ret:.4%}，约{net:.2f} USD'
        max_hold=int(self.cfg.get('pair_max_hold_seconds',172800))
        opened=self.state.get('pair',{}).get('opened_at')
        if max_hold > 0 and opened is not None and dec(self.client.now())-dec(opened) >= dec(max_hold):
            return '组合持仓超时'
        return None

    def tp_target(self,symbol):
        p=self.pos(symbol); long=dec(p['qty'])>0
        return bounded_price(self.markets[symbol],dec(p['entry'])*(dec('1.008') if long else dec('0.992')),'SELL' if long else 'BUY')

    def tp_tick(self,symbol):
        if self.state['exiting'] or not self.qty(symbol): return
        market=self.markets[symbol]; qty=abs(self.qty(symbol)); price=self.tp_target(symbol)
        active=self.active(symbol,{'T'})
        covered=sum(dec(r['body']['quantity'])-dec(r['filled']) for r in active)
        entry_complete=(symbol==PAIR[0] and any(
            r['symbol']==PAIR[0] and r['role']=='E' and r['terminal']
            and dec(r['filled'])==dec(r['body']['quantity'])
            for r in self.state['orders'].values()))
        # Once BTC G0 is fully filled, replace partial TPs with whole-position
        # protection. Keep only the splitting required by the exchange size cap.
        minimum_orders=int((qty/dec(market['maxOrderSize'])).to_integral_value(rounding=ROUND_UP))
        consolidate=entry_complete and (covered!=qty or len(active)>minimum_orders)
        if active and (consolidate or covered>qty or any(r['cancel_requested'] or dec(r['body']['price'])!=price
                          or r['body']['orderSide']!=('SELL' if self.qty(symbol)>0 else 'BUY') for r in active)):
            for rec in active: self.cancel(rec)
            return
        if self.active(symbol,{'X'}): return
        remaining=qty-covered
        while remaining>0 and not self.state['exiting']:
            amount=min(remaining,dec(market['maxOrderSize']))
            rec=self.submit(symbol,'T','SELL' if self.qty(symbol)>0 else 'BUY',amount,price,reduce=True)
            if rec is None: return
            remaining-=amount


    def flatten_all(self):
        self.begin_exit(self.state['exit_reason'] or '本轮退出')
        # Cancel ALL resting exposure and TPs before closing either position.
        for rec in self.active():
            if rec['role']!='X': self.cancel(rec)
        self.reconcile()
        if self.active(roles={'E','H','G','T'}): return
        for symbol in PAIR:
            if self.active(symbol,{'X'}): continue
            if self.qty(symbol):
                q=self.client.quote(symbol); side='SELL' if self.qty(symbol)>0 else 'BUY'
                self.submit(symbol,'X',side,min(abs(self.qty(symbol)),dec(self.markets[symbol]['maxOrderSize'])),
                            exit_limit(q,side,self.cfg,self.markets[symbol]),'IOC',True,True)
                self.reconcile()
        opens=self.reconcile()
        if any(self.qty(s) for s in PAIR) or self.active() or opens: return
        cycle=self.state['cycle']
        if self.state['exit_reason']=='外部真实仓位变化':
            self.event('complete','外部真实仓位变化，全部仓位归零\nBTC=0，ETH=0，双腿本轮挂单=0\n本轮结束，开始轮巡')
        elif self.state['exit_reason']=='首仓未成交或外部平仓':
            self.event('complete','首仓未成交或外部平仓\n全部仓位归零\nBTC=0，ETH=0，双腿本轮挂单=0\n本轮结束，开始下一轮')
        else:
            self.event('complete','全部仓位归零\nBTC=0，ETH=0，双腿本轮挂单=0\n本轮结束')
        self.state.update(last_completed_cycle=cycle,cycle=None,orders={},base_qty='0',known_qty='0',
                          managed={},exiting=False,exit_reason='',state='WAIT',recovery_required='',
                          cooldown_until=self.client.now()+self.cfg['cooldown_seconds'])
        self.state['pair'].update(base_qty={s:'0' for s in PAIR},base_btc_notional='0',base_eth_notional='0',
                                  btc_filled_notional='0',hedged_btc_notional='0',residual_notional='0',position_entries={})
        self.save()

    def next_scan_interval(self):
        """Fast fallback only while BTC fills or outstanding ETH hedges need attention.

        WebSocket wakeups remain immediate. Completed hedges and rounding dust
        use the normal scan interval; this does not change the D1 timeframe.
        """
        normal=self.cfg['scan_interval_sec']
        if self.state['exiting'] or not self.state['cycle']:
            return normal
        pending=bool(self.active(roles={'E','H'}))
        if not pending and self.account is not None and self.qty(PAIR[0]):
            btc,eth=self.notionals()
            missing=btc-eth
            market=self.markets.get(PAIR[1],{})
            threshold=dec(market.get('minOrderNotional',0))
            # An existing ETH average gives a conservative dust-size estimate;
            # hedge_tick still sizes against a freshly fetched executable quote.
            entry=dec(self.pos(PAIR[1]).get('entry',0))
            threshold=max(threshold,entry*dec(market.get('minOrderSize',0)))
            pending=missing>0 and missing>=threshold
        return min(normal,self.cfg.get('hedge_scan_interval_sec',5)) if pending else normal

    def wait_log(self, reason, **fields):
        """Read-only diagnostics; terminal failures must not affect trading decisions."""
        try:
            active=self.active()
            context={
                'BTC订单':sum(r['symbol']==PAIR[0] for r in active),
                'ETH订单':sum(r['symbol']==PAIR[1] for r in active),
                'BTC仓位':str(self.qty(PAIR[0])),
                'ETH仓位':str(self.qty(PAIR[1])),
                **fields,
            }
            details=' | '.join(f'{key}={value}' for key,value in context.items())
            print(f'[WAIT] reason={reason} | {details}',flush=True)
        except Exception:
            # Observability is a side channel, never authorization to skip a guard.
            pass

    def tick(self):
        self.reconcile()
        self.risk.update_daily()
        self.markets={s:self.client.market(s) for s in PAIR}
        if self.state['exiting']:
            self.wait_log('EXITING',exit_reason=self.state['exit_reason'])
            self.flatten_all(); return
        if self.state['cycle']:
            self.wait_log('CYCLE_ACTIVE',cycle=self.state['cycle'],state=self.state['state'])
            if all(self.qty(s) for s in PAIR):
                reason=self.pair_risk_trigger()
                if reason: self.begin_exit(reason)
            if self.state['daily'].get('halted'): self.begin_exit('日内亏损限制')
            if self.state['exiting']: self.flatten_all(); return
            old_grid=self.active(roles={'G'})
            for r in old_grid: self.cancel(r)
            if old_grid:
                self.reconcile()
                if self.active(roles={'G'}):
                    self.wait_log('CANCEL_PENDING',role='G')
                    return
            for r in self.active(PAIR[0],{'E'}):
                if self.client.now()-r['created_at']>=self.cfg['entry_timeout_sec']: self.cancel(r)
            if self.qty(PAIR[1]) and (not self.qty(PAIR[0]) or self.qty(PAIR[0])*self.qty(PAIR[1])>0):
                self.begin_exit('双腿方向或仓位异常'); self.flatten_all(); return
            if not any(self.qty(s) for s in PAIR) and not self.active(roles={'E','H'}):
                self.begin_exit('首仓未成交或外部平仓'); self.flatten_all(); return
            hedge_error=None
            try:
                self.hedge_tick()
            except SafetyError as exc:
                hedge_error=exc
            self.reconcile()
            if self.state['exiting']: self.flatten_all(); return
            # Paired mode exits on portfolio PnL; no individual T TP orders.
            reason=self.pair_risk_trigger()
            if reason:
                self.begin_exit(reason)
                self.flatten_all()
                return
            if hedge_error: raise hedge_error
            return
        if self.active():
            self.wait_log('ACTIVE_ORDER')
            return
        if any(self.qty(s) for s in PAIR):
            self.wait_log('POSITION_EXISTS')
            return
        if self.state['daily'].get('halted'):
            self.wait_log('DAILY_HALTED',day=self.state['daily'].get('day'),
                          max_daily_loss_usd=self.cfg['max_daily_loss_usd'],
                          max_daily_drawdown_pct=self.cfg['max_daily_drawdown_pct'])
            return
        if self.client.now()<self.state['cooldown_until']:
            self.wait_log('COOLDOWN',remaining=f"{max(0,self.state['cooldown_until']-self.client.now()):.1f}秒")
            return
        q=self.client.quote(PAIR[0])
        r=evaluate_hedge(self.client.candles('5m'),self.cfg,
                         ledger=self.state['ledger'],account_known=True,current_price=q['mid'],now=self.client.now())
        self.save()
        print(format_log(self.cfg['symbol'],r,self.cfg),flush=True)
        if not r['signal']: return
        if (q['ask']-q['bid'])/q['mid']*10000>dec(self.cfg['max_spread_bps']): raise SafetyError('价差超过上限')
        for m in self.markets.values(): self.client.verify_leverage(m)
        self.reconcile()
        q2=self.client.quote(PAIR[0])
        if abs(q2['mid']/q['mid']-1)>dec(self.cfg['max_signal_price_deviation_pct']): raise SafetyError('信号至挂单价格偏离过大')
        side='BUY' if r['side']=='LONG' else 'SELL'
        price=bounded_price(self.markets[PAIR[0]],q2['mid']*(1+dec(self.cfg['entry_limit_offset_pct'])*(-1 if side=='BUY' else 1)),side)
        if (side=='BUY' and price>=q2['bid']) or (side=='SELL' and price<=q2['ask']): raise SafetyError('首仓距离不足以位于盘口外侧')
        target=dec(self.account['equity'])*dec(self.cfg['first_order_size'])
        self.check_budget(PAIR[0],target,pair_reserve=True)
        qty=floor_step(target/price,self.markets[PAIR[0]]['stepSize'])
        self.state['cycle']=f"{r['bar_5m']:08x}"+uuid.uuid4().hex[:6]
        self.state['pair']['target_btc_notional']=str(target)
        self.save()
        self.submit(PAIR[0],'E',side,qty,price,'ALO')


def observe_pair_once(client,cfg,state_path):
    identity={'network':cfg['network'],'address':client.address,'account_index':client.account_index,
              'symbol':cfg['symbol'],'prefix':cfg['bot_prefix'],'dry_run':True}
    state,_=read_state(state_path,identity)
    client.sync_time()
    account=client.account()
    opens=[r for s in PAIR for r in client.open_orders(s)]
    r=evaluate_hedge(client.candles('5m'),cfg,ledger=state['ledger'],
        account_known=True,position_side='OCCUPIED' if any(account['positions'].get(s) for s in PAIR) else '',
        has_entry_order=bool(opens),current_price=client.quote(PAIR[0])['mid'],now=client.now())
    atomic_json(state_path,state)
    print(format_log(cfg['symbol'],r,cfg),flush=True)
    return r


# ============================================================
# MAIN 主程序入口
# ============================================================

class Bot(BotState):
    """组合六个模块；这里只编排每次扫描的调用顺序。"""
    def __init__(self, cfg, client, stream, path, emit=log):
        super().__init__(cfg, client, stream, path, emit)
        self.orders = OrderManager(self)
        self.grid = GridManager(self)
        self.tp = TakeProfitManager(self)
        self.entry = EntryManager(self)
        self.exit = ExitManager(self)
        self.risk = RiskRecoveryManager(self)
        self.notifications = TelegramNotifications(self)
        self.terminal_ready = False

    def recover(self):
        result = self.risk.recover()
        self.notifications.safe('baseline')
        self.terminal_ready = True
        return result

    @staticmethod
    def expected_qty(state):
        return RiskRecoveryManager.expected_qty(state)

    def rebuild_managed(self):
        return self.risk.rebuild_managed()

    def reconcile(self):
        before = self.state
        result = self.risk.reconcile()
        log_confirmed_trade_events(self, before)
        self.notifications.safe('observe')
        return result

    def check_open_risk(self, q):
        return self.risk.check_open_risk(q)

    def update_daily(self):
        return self.risk.update_daily()

    def begin_exit(self, reason):
        return self.exit.begin_exit(reason)

    def finish_cycle(self):
        result = self.exit.finish_cycle()
        if result:
            self.notifications.safe('finished')
        return result

    def exit_tick(self, q):
        return self.exit.exit_tick(q)

    def tick(self):
        self.reconcile()
        self.risk.require_confirmed_state()
        self.market=self.client.market()
        self.update_daily()
        q=self.client.quote()
        pos=self.position()
        self.exit.check_triggers(q, pos)
        if self.state['exiting']:
            self.exit_tick(q)
            return
        self.entry.expire_pending()
        # Existing position management must not depend on a successful candle fetch.
        if pos:
            self.tp.tick(q)
            if self.state['exiting']:
                self.exit_tick(q)
                return
        if pos:
            # Replacement TP is reconciled before any next exposure layer.
            if not any(x['cancel_requested'] or x['status'] in ('INTENT_SAVED','OUTCOME_UNKNOWN','ACK_ONLY')
                       for x in self.orders.active()):
                self.grid.tick(q)
            return
        # Log the RSI-only decision for flat accounts only.
        r=evaluate(None,self.client.candles(self.cfg['entry_timeframe']),self.cfg,
                   ledger=self.state['ledger'],position_side=('LONG' if dec(pos['qty'])>0 else 'SHORT') if pos else '',
                   has_entry_order=bool(self.orders.active()),account_known=True,current_price=q['mid'],now=self.client.now())
        self.save()  # Persist signal dedup before log or order submission.
        print(format_log(self.cfg['symbol'],r,self.cfg),flush=True)
        self.entry.tick(r, q)

def observe_once(client,cfg,state_path):
    identity={'network':cfg['network'],'address':client.address,'account_index':client.account_index,
              'symbol':cfg['symbol'],'prefix':cfg['bot_prefix'],'dry_run':True}
    state,_=read_state(state_path,identity)
    client.sync_time()
    market=client.market()
    q=client.quote()
    f=client.candles(cfg['entry_timeframe'])
    known=False
    position=''
    pending=False
    if client.address:
        try:
            account=client.account()
            rows=client.open_orders()
            qty=dec(account['positions'].get(cfg['symbol'],{}).get('qty',0))
            position='LONG' if qty>0 else 'SHORT' if qty<0 else ''
            pending=bool(rows)
            known=True
            log('DRY_RUN_ACCOUNT',position=position or 'FLAT',open_orders=len(rows),
                recovery_state='GRID_'+position if position else 'ORDER_PENDING' if pending else 'WAIT')
        except SafetyError as exc:
            log('WAIT',reason=str(exc))
    r=evaluate(None,f,cfg,ledger=state['ledger'],position_side=position,has_entry_order=pending,
               account_known=known,current_price=q['mid'],now=client.now())
    atomic_json(state_path,state)
    print(format_log(cfg['symbol'],r,cfg),flush=True)
    if r['signal'] and cfg['entry_limit_offset_pct'] is not None:
        side='BUY' if r['side']=='LONG' else 'SELL'
        price=bounded_price(market,q['mid']*(1+dec(cfg['entry_limit_offset_pct'])*(1 if side=='SELL' else -1)),side)
        log('DRY_RUN',side=side,limit=price,size=cfg['first_order_size'],size_unit=cfg['size_unit'],submitted=False)
    return r

def main(argv=None):
    parser=argparse.ArgumentParser(description='Arcus BTC 单文件机器人；默认遵守config.json的dry_run')
    parser.add_argument('--config',type=Path,default=ROOT/'config.json')
    parser.add_argument('--once',action='store_true',help='只运行一轮')
    parser.add_argument('--check',action='store_true',help='本地配置和依赖检查，不联网')
    parser.add_argument('--self-test',action='store_true',help='内置离线生命周期自检，不连接交易所')
    args=parser.parse_args(argv)
    cfg=load_config(args.config)
    if args.self_test:
        legacy_result=run_self_tests(cfg)
        pair_result=run_pair_tests(cfg)
        return max(legacy_result,pair_result)
    blockers=live_blockers(cfg)
    log('CONFIG',symbol=cfg['symbol'],dry_run=cfg['dry_run'],needs_confirmation=blockers)
    if args.check:
        present={field:bool(credential_value(cfg,field,env)) for field,env in
                 (('wallet_address','wallet_address_env'),('api_signing_key','signing_key_env'))}
        log('CHECK',syntax_import_config='PASS',parameters_ready=not blockers,
            credentials_present=present,account_verified=False)
        return 0
    if not cfg['dry_run'] and blockers:
        raise SafetyError('; '.join(blockers))
    client=ArcusClient(cfg)
    # One live process per account+market even if another config changes bot_prefix.
    identity_text=f"{cfg['network']}:{client.address}:{cfg['account_index']}:{cfg['symbol']}"
    folder=ROOT/cfg['runtime_dir']/hashlib.sha256(identity_text.encode()).hexdigest()[:16]
    folder.mkdir(parents=True,exist_ok=True)
    filename='dry_run.json' if cfg['dry_run'] else 'state.json'
    path=folder/filename
    stream=None
    with (folder/('dry_run.lock' if cfg['dry_run'] else 'live.lock')).open('a') as lock:
        acquire_process_lock(lock)
        try:
            if not cfg['dry_run']:
                client.account_params()
                client.sync_time()
                client.load_signer()
                client.verify_key()
                stream=OrderStream(client)
                stream.start()
                deadline=time.monotonic()+cfg['ws_start_timeout_sec']
                while not stream.healthy() and time.monotonic()<deadline:
                    time.sleep(0.1)
                if not stream.healthy():
                    raise SafetyError('订单实时订阅启动失败；尚未下单')
                bot=(HedgeBot if cfg.get('hedge_enabled') else Bot)(cfg,client,stream,path)
                bot.recover()
                bot.notifications.safe('startup')
            dry_notifications=TelegramNotifications(cfg=cfg) if cfg['dry_run'] else None
            while True:
                try:
                    if cfg['dry_run']:
                        observed=(observe_pair_once if cfg.get('hedge_enabled') else observe_once)(client,cfg,path)
                        dry_notifications.safe('startup',observed['grid_state'] or observed['state'])
                    else:
                        if cfg.get('hedge_enabled'): stream.wake_event.clear()
                        bot.tick()
                except (SafetyError,KeyError,ValueError,TypeError) as exc:
                    # Programming/schema surprises cannot authorize orders.
                    log('WAIT',reason=str(exc) if isinstance(exc,SafetyError) else '数据字段异常：'+type(exc).__name__)
                    if args.once:
                        return 2
                if args.once:
                    return 0
                if stream and cfg.get('hedge_enabled'):
                    stream.wake_event.wait(bot.next_scan_interval())
                else:
                    time.sleep(cfg['scan_interval_sec'])
        finally:
            if stream:
                stream.stop()

# ============================================================
# SELF TEST 自检
# ============================================================

def run_self_tests(base_cfg):
    import unittest
    from unittest.mock import patch
    base_cfg=copy.deepcopy(base_cfg)
    base_cfg.update(hedge_enabled=False,grid_enabled=True,rsi_period=7,rsi_long_threshold=30,
                    rsi_short_threshold=70,first_order_size=1.5,entry_timeout_sec=90,take_profit_pct=0.007)
    # Tests never copy real file-based credentials to temporary fixtures.
    base_cfg.update(wallet_address='',api_signing_key='',telegram_enabled=False,
                    telegram_bot_token='',telegram_chat_id='')

    class Feed:
        def healthy(self): return True
        def find(self,*args): return None

    class FakeClient:
        """Simulation contract only, not proof of a live Arcus order fill."""
        def __init__(self,cfg):
            self.cfg=cfg
            self.address='0x'+'1'*40
            self.account_index=0
            self.t=1800000000.0
            self.rows={}
            self.qty=Decimal('0')
            self.entry=Decimal('0')
            self.seq=1
            self.placed=0
            self.canceled=0
            self.timeout_after_submit=False
            self.cancel_pending=False
            self.q={'bid':Decimal('99.9'),'ask':Decimal('100.1'),'mid':Decimal('100')}
            self.m={'marketId':1,'marketDisplayName':'BTC-USD','status':'ONLINE',
                    'tickSize':'0.1','stepSize':'0.001','minOrderSize':'0.001','maxOrderSize':'100',
                    'minOrderNotional':'0.1','initialMarginFraction':'0.02','tickTiers':[]}
        def now(self): return self.t
        def now_ns(self): return int(self.t*1e9)
        def nonce(self): self.t+=0.000001; return self.now_ns()
        def sync_time(self): return self.t
        def account_params(self): return {'address':self.address,'accountIndex':0}
        def market(self): return copy.deepcopy(self.m)
        def quote(self): return self.q.copy()
        def verify_leverage(self,m): pass
        def account(self):
            positions={}
            if self.qty:
                positions={'BTC-USD':{'qty':str(self.qty),'entry':str(self.entry),'mark':'100','notional':str(abs(self.qty)*100)}}
            return {'equity':'10000','free':'10000','deposits':'10000','sequence':self.seq,'positions':positions}
        def open_orders(self): return [copy.deepcopy(r) for r in self.rows.values() if not order_terminal(r)]
        def order_history(self,start=None): return list(copy.deepcopy(self.rows).values())
        def order(self,oid): return copy.deepcopy(self.rows.get(oid))
        def place(self,body,market):
            self.placed+=1
            oid='o'+str(self.placed)
            self.rows[oid]=dict(orderId=oid,clientId=body['clientId'],marketId=1,marketDisplayName='BTC-USD',
                address=self.address,accountIndex=0,side=body['orderSide'],status='OPEN',state='OPEN',
                originalSize=body['quantity'],remainingSize=body['quantity'],filledSize='0',price=body['price'],
                timeInForce=body['timeInForce'],reduceOnly=body['reduceOnly'],createdAt=int(self.t*1e6),
                updatedAt=int(self.t*1e6),sequenceNumber=self.seq)
            if self.timeout_after_submit:
                raise UnknownOutcome('模拟提交后响应丢失')
            return {'orderId':oid,'clientId':body['clientId'],'status':'ACK'}
        def cancel(self,r):
            self.canceled+=1
            if self.cancel_pending: raise UnknownOutcome('模拟撤单延迟')
            row=self.rows[r['order_id']]
            row.update(status='CANCELED',state='CANCELED')
            self.seq+=1
            self.t+=1
            row.update(sequenceNumber=self.seq,updatedAt=int(self.t*1e6))
            return {'status':'CANCEL_ACKNOWLEDGED'}
        def fill(self,oid,amount,price=None):
            row=self.rows[oid]
            n=dec(amount)
            px=dec(price or row['price'])
            old=dec(row['filledSize'])
            total=old+n
            if n>dec(row['remainingSize']): raise ValueError('overfill')
            signed=n if row['side']=='BUY' else -n
            if row['reduceOnly'] and (not self.qty or self.qty*signed>=0 or n>abs(self.qty)):
                row.update(status='REJECTED',state='REJECTED')
                return
            if not row['reduceOnly']:
                self.entry=(abs(self.qty)*self.entry+n*px)/(abs(self.qty)+n)
            self.qty+=signed
            if not self.qty: self.entry=Decimal('0')
            self.seq+=1; self.t+=1
            row.update(filledSize=str(total),remainingSize=str(dec(row['originalSize'])-total),
                       avgFillPrice=str((old*dec(row.get('avgFillPrice',0))+n*px)/total),
                       status='FILLED' if total==dec(row['originalSize']) else 'OPEN',
                       state='FILLED' if total==dec(row['originalSize']) else 'PARTIALLY_FILLED',
                       sequenceNumber=self.seq,updatedAt=int(self.t*1e6))
        def candles(self,timeframe):
            return bars({'1h':3600,'15m':900,'5m':300}[timeframe],now=int(self.t//3600)*3600)

    def bars(step,down=False,now=1800000000):
        now=now//3600*3600
        out=[]
        for i in range(200):
            p=1000-i if down else 1000+i
            out.append(dict(openTime=(now-step*(200-i))*1000000,isFinal=True,
                            open=p,high=p+2,low=p-2,close=p))
        return out

    class Tests(unittest.TestCase):
        def setUp(self):
            self.tmp=tempfile.TemporaryDirectory()
            self.cfg=copy.deepcopy(base_cfg)
            # Test fixtures only. Never persist these strategy choices in user config.
            self.cfg.update(dry_run=False,sizing_confirmed=True,grid_mode='fixed',tp_mode='fixed_limit',entry_limit_offset_pct=0.01,
                            take_profit_pct=0.007,first_order_size=1,size_unit='base_qty',
                            grid_order_sizes=[1]*self.cfg['grid_max_layers'],max_spread_bps=100)
            self.client=FakeClient(self.cfg)
            self.path=Path(self.tmp.name)/'state.json'
            self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            self.bot.recover()
            self.now=1800000000//3600*3600
        def tearDown(self): self.tmp.cleanup()
        def signal(self,down=False,prev=29,cur=31,ledger=None,**kw):
            with patch(__name__+'.calc_rsi',side_effect=[cur,prev]):
                return evaluate(bars(3600,down),bars(900),self.cfg,five=bars(300),now=self.now,
                                ledger=ledger,account_known=True,**kw)
        def entry(self,short=False):
            self.bot.state.update(cycle=f'{self.now:08x}abcdef',ledger={'last_signal_bar':self.now-900,
                                  'last_signal_side':'SHORT' if short else 'LONG','signal_time':self.now})
            return self.bot.orders.submit('E',0,'SELL' if short else 'BUY',Decimal('1'),Decimal('101') if short else Decimal('99'))
        def filled_entry(self,short=False):
            r=self.entry(short)
            self.client.fill(r['order_id'],'1')
            self.bot.reconcile()
            return r
        def test_01_config_import(self):
            validate_config(self.cfg)
            self.assertIn('entry_limit_offset_pct',base_cfg)
            self.assertNotIn('from indicators import',Path(__file__).read_text().split('# SELF TEST 自检')[0])
        def test_02_long_short_signals(self):
            self.assertEqual(self.signal()['state'],'LONG_ORDER_PENDING')
            self.assertEqual(self.signal(True,71,69)['state'],'SHORT_ORDER_PENDING')
            for prev,cur,expected in [(29,31,True),(20,35,True),(30,31,True),
                                      (20,21,False),(31,29,False),(31,32,False),(29,30,False)]:
                with self.subTest(side='LONG',previous=prev,current=cur):
                    r=self.signal(prev=prev,cur=cur)
                    self.assertEqual(r['signal'],expected)
                    self.assertEqual(r['side'],'LONG' if expected else '')
            for prev,cur,expected in [(71,69,True),(80,65,True),(70,69,True),
                                      (79,78,False),(69,71,False),(69,68,False),(71,70,False)]:
                with self.subTest(side='SHORT',previous=prev,current=cur):
                    r=self.signal(True,prev,cur)
                    self.assertEqual(r['signal'],expected)
                    self.assertEqual(r['side'],'SHORT' if expected else '')
        def test_03_ema_adx_do_not_gate_rsi(self):
            for adx in (0,24,24.9,25,60,100):
                with self.subTest(adx=adx),\
                     patch(__name__+'.calc_adx',return_value=adx) as adx_calc,\
                     patch(__name__+'.calc_ema_series',side_effect=AssertionError('D1不得计算EMA')):
                    # Opposing 1H candle trends must not block the RSI direction.
                    self.assertEqual(self.signal(True,29,31)['side'],'LONG')
                    self.assertEqual(self.signal(False,71,69)['side'],'SHORT')
                    adx_calc.assert_not_called()
        def test_04_closed_only(self):
            f=bars(900)
            f.append(dict(f[-1],openTime=self.now*1000000,isFinal=True,close=99999))
            self.assertEqual(len(closed_rows(f,900,14,self.now)),200)
            for data in (f[:-2],[],f+[f[-2]]):
                self.assertFalse(evaluate(bars(3600),data,self.cfg,now=self.now,account_known=True)['signal'])
        def test_05_signal_dedup_restart(self):
            ledger={}
            self.assertTrue(self.signal(ledger=ledger)['signal'])
            ledger=json.loads(json.dumps(ledger))
            self.assertFalse(self.signal(ledger=ledger)['signal'])
            self.assertFalse(self.signal(True,71,69,ledger)['signal'])
        def test_06_account_gates(self):
            self.assertFalse(self.signal(position_side='LONG')['signal'])
            self.assertFalse(self.signal(has_entry_order=True)['signal'])
            self.assertFalse(evaluate(bars(3600),bars(900),self.cfg,now=self.now)['signal'])
        def test_07_ack_partial_full(self):
            r=self.entry()
            self.bot.reconcile()
            self.assertEqual(self.bot.state['state'],'LONG_ORDER_PENDING')
            self.client.fill(r['order_id'],'0.4')
            self.bot.reconcile()
            self.assertEqual(self.bot.state['state'],'GRID_LONG')
            self.assertEqual(self.bot.state['managed']['layers'],1)
            self.client.fill(r['order_id'],'0.6')
            self.bot.reconcile()
            self.assertEqual(self.bot.state['managed']['layers'],1)
        def test_08_timeout_and_duplicate(self):
            self.client.timeout_after_submit=True
            r=self.entry()
            self.assertEqual(r['status'],'OUTCOME_UNKNOWN')
            with self.assertRaises(SafetyError): self.entry()
            self.bot.reconcile()
            self.assertEqual(self.client.placed,1)
            self.assertEqual(self.bot.orders.active()[0]['order_id'],'o1')
        def test_09_missing_order_never_resubmit(self):
            r=self.entry()
            self.client.rows.clear()
            with self.assertRaises(SafetyError): self.bot.reconcile()
            with self.assertRaises(SafetyError): self.entry()
            self.assertEqual(self.client.placed,1)
        def test_10_long_grid_tp_refresh(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q)
            self.bot.reconcile()
            oldtp=self.bot.orders.active({'T'})[0]
            self.bot.grid.tick(self.client.q)
            grid=self.bot.orders.active({'G'})[0]
            self.assertLess(dec(grid['body']['price']),Decimal('99'))
            self.client.fill(grid['order_id'],'0.5')
            self.bot.reconcile()
            newavg=dec(self.bot.position()['entry'])
            self.assertLess(newavg,Decimal('99'))
            self.bot.tp.tick(self.client.q)
            self.assertTrue(self.bot.state['orders'][oldtp['body']['clientId']]['cancel_requested'])
            self.bot.reconcile()
            self.bot.tp.tick(self.client.q)
            tp=self.bot.orders.active({'T'})[0]
            self.assertEqual(dec(tp['body']['quantity']),Decimal('1.5'))
            self.assertGreater(dec(tp['body']['price']),newavg)
            self.assertTrue(tp['body']['reduceOnly'])
        def test_11_short_grid_tp(self):
            self.filled_entry(True)
            self.bot.tp.tick(self.client.q)
            self.bot.reconcile()
            self.bot.grid.tick(self.client.q)
            grid=self.bot.orders.active({'G'})[0]
            self.assertGreater(dec(grid['body']['price']),Decimal('101'))
            tp=self.bot.orders.active({'T'})[0]
            self.assertEqual(tp['body']['orderSide'],'BUY')
            self.assertLess(dec(tp['body']['price']),Decimal('101'))
        def test_12_restart_existing_journal(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q)
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            restarted.tp.tick(self.client.q)
            self.assertEqual(self.client.placed,2)
            self.assertEqual(restarted.state['state'],'GRID_LONG')
        def test_13_rebuild_missing_journal(self):
            self.filled_entry(True)
            self.path.unlink()
            rebuilt=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            rebuilt.recover()
            self.assertEqual(rebuilt.state['state'],'GRID_SHORT')
            self.assertEqual(rebuilt.state['managed']['layers'],1)
            self.assertFalse(rebuilt.state['recovery_required'])
        def test_14_cancel_reject_no_fill(self):
            r=self.entry()
            self.client.rows[r['order_id']].update(status='REJECTED',state='REJECTED')
            self.bot.reconcile()
            self.assertFalse(self.bot.position())
            self.assertFalse(self.bot.orders.active())
            self.assertEqual(self.bot.state['state'],'WAIT')
        def test_15_cancel_ack_not_final(self):
            r=self.entry()
            self.client.cancel_pending=True
            self.bot.orders.cancel(r)
            self.bot.reconcile()
            self.assertEqual(len(self.bot.orders.active()),1)
            with self.assertRaises(SafetyError): self.entry()
        def test_16_exit_cancels_grid_before_wait(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            self.bot.grid.tick(self.client.q); self.bot.reconcile()
            tp=self.bot.orders.active({'T'})[0]
            self.client.fill(tp['order_id'],'1')
            self.bot.reconcile()
            self.assertEqual(self.bot.state['state'],'EXITING')
            self.bot.exit_tick(self.client.q)
            self.bot.reconcile(); self.bot.exit_tick(self.client.q)
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.client.open_orders())
            self.assertTrue(self.bot.state['ledger'])
        def test_17_dry_run_write_protection(self):
            cfg=copy.deepcopy(self.cfg); cfg['dry_run']=True
            c=ArcusClient(cfg)
            with patch.object(c.session,'request') as request:
                with self.assertRaises(SafetyError): c.request('POST','/v1/placeOrder',body={})
                request.assert_not_called()
        def test_18_typed_signature(self):
            body=make_body(self.client,self.client.m,'BUY',1,99,'ALO',False,'test1')
            payload=order_payload(body,self.client.m)
            self.assertEqual(payload['t'],3)
            self.assertEqual(payload['p'],990)
            self.assertEqual(payload['q'],1000)
            self.assertEqual(payload['g'],int(body['goodTilTime'])*1000)
            key=Ed25519PrivateKey.from_private_bytes(bytes(range(32)))
            key.public_key().verify(key.sign(canonical(payload)),canonical(payload))
        def test_19_indicators_unchanged(self):
            self.assertEqual(calc_rsi(list(range(1,30)),12),100)
            self.assertEqual(calc_rsi(list(range(30,1,-1)),12),0)
            self.assertEqual(calc_rsi([10]*30,12),50)
            self.assertEqual(calc_ema_series([10]*60,20)[-1],10)
            self.assertEqual(calc_adx(list(range(3,43)),list(range(1,41)),list(range(2,42)),14),100)
        def test_20_mismatch_and_corrupt_state(self):
            self.entry()
            self.client.qty=Decimal('8'); self.client.entry=Decimal('100')
            self.bot.reconcile()
            self.assertTrue(self.bot.state['managed']['adopted_g0'])
            with self.assertRaises(SafetyError): self.bot.risk.require_confirmed_state()
            self.assertTrue(self.bot.orders.active({'R'}))
            self.path.write_text('{bad')
            with self.assertRaises(SafetyError): Bot(self.cfg,self.client,Feed(),self.path)
        def test_21_legacy_trailing(self):
            pos={'qty':'1','entry':'100'}
            managed={'layers':2}
            self.assertEqual(legacy_exit_reason(pos,managed,{'bid':dec('102'),'ask':dec('102.1')},self.cfg),'')
            self.assertEqual(legacy_exit_reason(pos,managed,{'bid':dec('101.7'),'ask':dec('101.8')},self.cfg),'盈利回撤退出')
        def test_22_grid_duplicate(self):
            self.filled_entry()
            self.bot.grid.tick(self.client.q)
            self.bot.grid.tick(self.client.q)
            self.assertEqual(len(self.bot.orders.active({'G'})),1)
        def test_23_no_journal_unknown_position(self):
            self.path.unlink()
            self.client.qty=Decimal('1'); self.client.entry=Decimal('100')
            b=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            b.recover()
            self.assertEqual(b.state['state'],'GRID_LONG')
            self.assertFalse(b.state['recovery_required'])
            self.assertEqual(b.state['managed']['grid_layer'],0)
            b.tick()
            self.assertEqual(len(b.orders.active({'T'})),1)
            self.assertFalse(b.orders.active({'E'}))
        def test_24_order_account_lag(self):
            r=self.entry()
            self.client.fill(r['order_id'],'1')
            self.client.qty=Decimal('0')
            with self.assertRaises(SafetyError): self.bot.reconcile()
            self.assertEqual(self.bot.state['orders'][r['body']['clientId']]['filled'],'0')
        def test_25_main_entry_limit_paths(self):
            for down in (False,True):
                client=FakeClient(self.cfg)
                bot=Bot(self.cfg,client,Feed(),Path(self.tmp.name)/('short.json' if down else 'long.json'),emit=lambda *a,**k:None)
                bot.recover()
                # Exercise actual evaluate -> Bot.tick -> ALO submission, not a mocked signal.
                with patch.object(client,'candles',side_effect=lambda tf: bars({'1h':3600,'15m':900,'5m':300}[tf],down,self.now)),\
                     patch(__name__+'.calc_rsi',side_effect=[69,71] if down else [31,29]):
                    bot.tick()
                order=bot.orders.active({'E'})[0]
                self.assertEqual(order['body']['orderSide'],'SELL' if down else 'BUY')
                self.assertEqual(order['body']['timeInForce'],'ALO')
                expected=client.q['mid']*(1+dec(self.cfg['entry_limit_offset_pct'])*(1 if down else -1))
                self.assertEqual(dec(order['body']['price']),expected)
                if down:
                    self.assertGreater(dec(order['body']['price']),client.q['ask'])
                else:
                    self.assertLess(dec(order['body']['price']),client.q['bid'])
            for down,prev,cur in [(False,49,51),(True,51,49),(False,22,23),
                                   (False,21,22),(True,77,76),(True,79,77)]:
                with self.subTest(down=down,previous=prev,current=cur):
                    client=FakeClient(self.cfg)
                    path=Path(self.tmp.name)/f'no-entry-{down}-{prev}-{cur}.json'
                    bot=Bot(self.cfg,client,Feed(),path,emit=lambda *a,**k:None)
                    bot.recover()
                    with patch.object(client,'candles',side_effect=lambda tf: bars({'1h':3600,'15m':900,'5m':300}[tf],down,self.now)),\
                         patch(__name__+'.calc_rsi',side_effect=[cur,prev]):
                        bot.tick()
                    self.assertEqual(client.placed,0)
                    self.assertFalse(bot.orders.active({'E'}))
        def test_26_partial_entry_timeout(self):
            r=self.entry()
            self.client.fill(r['order_id'],'0.4')
            self.client.t+=self.cfg['entry_timeout_sec']+1
            self.bot.tick()
            self.assertTrue(self.bot.state['orders'][r['body']['clientId']]['cancel_requested'])
            self.assertEqual(self.client.canceled,1)
        def test_27_partial_tp_cancels_resting_grid(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            self.bot.grid.tick(self.client.q); self.bot.reconcile()
            tp=self.bot.orders.active({'T'})[0]
            self.client.fill(tp['order_id'],'0.3')
            self.bot.reconcile(); self.bot.exit_tick(self.client.q)
            self.assertEqual(self.bot.state['state'],'EXITING')
            self.assertTrue(self.bot.orders.active({'G'})[0]['cancel_requested'])
            self.assertEqual(dec(self.bot.position()['qty']),Decimal('0.7'))
        def test_28_tp_cancel_fill_race(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            tp=self.bot.orders.active({'T'})[0]
            self.client.cancel_pending=True
            self.bot.orders.cancel(tp)
            self.client.fill(tp['order_id'],'1')
            self.bot.reconcile(); self.bot.exit_tick(self.client.q)
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertEqual(self.client.placed,2)
        def test_29_grid_limit_max_layers(self):
            self.filled_entry()
            for layer in range(1,self.cfg['grid_max_layers']+1):
                self.bot.grid.tick(self.client.q)
                r=self.bot.orders.active({'G'})[0]
                self.client.fill(r['order_id'],r['body']['quantity'])
                self.bot.reconcile()
            count=self.client.placed
            self.bot.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,count)
            self.assertEqual(self.bot.state['managed']['layers'],self.cfg['grid_max_layers']+1)
        def test_30_readonly_observer(self):
            cfg=copy.deepcopy(self.cfg); cfg['dry_run']=True
            client=FakeClient(cfg)
            observe_once(client,cfg,Path(self.tmp.name)/'dry.json')
            self.assertEqual(client.placed,0)
            self.assertEqual(client.canceled,0)
        def test_31_ioc_partial_terminal(self):
            r=self.entry()
            row=copy.deepcopy(self.client.rows[r['order_id']])
            row.update(timeInForce='IOC',status='CANCELED',state='PARTIALLY_FILLED',remainingSize='0.5',filledSize='0.5')
            self.assertTrue(order_terminal(row))
        def test_32_tp_protected_when_candles_fail(self):
            self.filled_entry()
            with patch.object(self.client,'candles',side_effect=SafetyError('行情暂不可用')) as candles:
                self.bot.tick()
                candles.assert_not_called()
            self.assertEqual(len(self.bot.orders.active({'T'})),1)
        def test_33_mutation_never_network_retry(self):
            c=ArcusClient(self.cfg)
            with patch.object(c.session,'request',side_effect=requests.Timeout) as request:
                with self.assertRaises(UnknownOutcome):
                    c.request('POST','/v1/placeOrder',body={})
                self.assertEqual(request.call_count,1)
        def test_34_cancel_signing_by_id_and_client(self):
            c=ArcusClient(self.cfg)
            c.address=self.client.address
            record={'order_id':'server-123','body':{'marketId':1,'clientId':'client-123'}}
            for by_id in (True,False):
                record['order_id']='server-123' if by_id else None
                with patch.object(c,'nonce',return_value=1800000000000000000),\
                     patch.object(c,'signed_headers',return_value={}) as signed,\
                     patch.object(c,'request',return_value={'status':'CANCEL_ACKNOWLEDGED'}) as request:
                    c.cancel(record)
                    payload=signed.call_args.args[1]
                    self.assertEqual(payload['op'],2)
                    self.assertEqual(payload['id' if by_id else 'c'],'server-123' if by_id else 'client-123')
                    self.assertNotIn('p',payload)
                    self.assertEqual(request.call_args.args[1],'/v1/cancelOrder')
        def test_35_server_clock_retries_slow_sample(self):
            c=ArcusClient(self.cfg)
            with patch.object(c,'request',return_value={'timeNs':1800000000000000000}),\
                 patch('time.monotonic_ns',side_effect=[0,6000000000,7000000000,7200000000]),\
                 patch('time.sleep'):
                self.assertEqual(c.sync_time(),1800000000)
                self.assertEqual(c.clock_mono,7200000000)
        def test_36_equity_notional_sizes_not_leveraged_twice(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(size_unit='equity_fraction',leverage=40,
                       max_symbol_equity_pct=3.5,max_account_equity_pct=3.5)
            account={'equity':'100','free':'100','positions':{}}
            q={'bid':dec('100'),'ask':dec('100'),'mid':dec('100')}
            held=dec(0)
            amounts=[]
            for multiple in (0.5,1,2):
                size=opening_quantity(cfg,account,{'qty':str(held)},self.client.m,q,100,multiple)
                amounts.append(size*100)
                held+=size
            self.assertEqual(amounts,[dec(50),dec(100),dec(200)])
            self.assertEqual(sum(amounts)/40,dec('8.75'))
        def test_37_nominal_cap_remains_enforced(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(size_unit='equity_fraction',max_symbol_equity_pct=3.5,max_account_equity_pct=3.5)
            account={'equity':'100','free':'100','positions':{}}
            q={'bid':dec('100'),'ask':dec('100'),'mid':dec('100')}
            size=opening_quantity(cfg,account,{'qty':'3'},self.client.m,q,100,2)
            self.assertEqual(size,dec('0.5'))
            with self.assertRaises(SafetyError):
                opening_quantity(cfg,account,{'qty':'3.5'},self.client.m,q,100,2)
        def test_38_config_allows_notional_over_equity(self):
            cfg=copy.deepcopy(base_cfg)
            cfg.update(size_unit='equity_fraction',first_order_size=0.5,grid_max_layers=2,
                       grid_order_sizes=[1,2],grid_spacings=[0.01,0.02],max_symbol_equity_pct=3.5,max_account_equity_pct=3.5)
            p=Path(self.tmp.name)/'config.json'
            p.write_text(json.dumps(cfg))
            self.assertEqual(load_config(p)['grid_order_sizes'],[1,2])
            cfg['max_symbol_equity_pct']=0.5
            p.write_text(json.dumps(cfg))
            with self.assertRaises(SafetyError): load_config(p)
        def test_39_file_credentials_take_precedence(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(wallet_address='0x'+'1'*40,api_signing_key=bytes(range(32)).hex())
            with patch.dict(os.environ,{cfg['wallet_address_env']:'0x'+'2'*40,
                                        cfg['signing_key_env']:'invalid-env-value'}):
                client=ArcusClient(cfg)
                self.assertEqual(client.account_params()['address'],cfg['wallet_address'])
                client.load_signer()
                expected=Ed25519PrivateKey.from_private_bytes(bytes(range(32))).public_key().public_bytes(Encoding.Raw,PublicFormat.Raw).hex()
                self.assertEqual(client.api_key,expected)
        def test_40_empty_file_credentials_use_environment(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(wallet_address='',api_signing_key='')
            with patch.dict(os.environ,{cfg['wallet_address_env']:'0x'+'2'*40,
                                        cfg['signing_key_env']:bytes(range(32)).hex()}):
                client=ArcusClient(cfg)
                self.assertEqual(client.account_params()['address'],'0x'+'2'*40)
                client.load_signer()
                self.assertIsNotNone(client.key)
        def test_41_signal_module_never_submits(self):
            with patch.object(self.client,'place',side_effect=AssertionError('D1不得下单')):
                self.assertTrue(self.signal()['signal'])
                self.assertTrue(self.signal(True,71,69)['signal'])
            self.assertEqual(self.client.placed,0)

        def test_42_module_routing_order(self):
            events=[]
            def wrap(obj,name,label):
                original=getattr(obj,name)
                def call(*args,**kwargs):
                    events.append(label)
                    return original(*args,**kwargs)
                return patch.object(obj,name,side_effect=call)
            with wrap(self.bot.risk,'reconcile','D5'),\
                 wrap(self.bot.exit,'check_triggers','D4'),\
                 wrap(self.bot.entry,'expire_pending','D2_timeout'),\
                 patch(__name__+'.evaluate',wraps=evaluate) as signal,\
                 wrap(self.bot.entry,'tick','D2_entry'),\
                 patch('builtins.print'):
                self.bot.tick()
            self.assertEqual(events,['D5','D4','D2_timeout','D2_entry'])
            signal.assert_called_once()
            self.assertEqual(self.client.placed,0)

        def test_43_recovery_blocks_all_strategy_modules(self):
            self.bot.state['recovery_required']='模拟待核对仓位'
            with patch.object(self.bot.entry,'tick') as entry,\
                 patch.object(self.bot.grid,'tick') as grid,\
                 patch.object(self.bot.tp,'tick') as tp,\
                 patch(__name__+'.evaluate') as signal:
                with self.assertRaises(SafetyError): self.bot.tick()
                for call in (entry,grid,tp,signal): call.assert_not_called()
            self.assertEqual(self.client.placed,0)

        def test_44_grid_cannot_create_first_entry(self):
            self.bot.grid.tick(self.client.quote())
            self.assertEqual(self.client.placed,0)
            self.assertFalse(self.bot.orders.active())

        def test_45_exit_module_reduce_only_and_cleanup(self):
            self.filled_entry()
            self.bot.begin_exit('价格止损')
            self.bot.exit_tick(self.client.quote())
            close=self.bot.orders.active({'X'})[0]
            self.assertTrue(close['body']['reduceOnly'])
            self.assertEqual(close['body']['orderSide'],'SELL')
            self.client.fill(close['order_id'],close['body']['quantity'])
            self.bot.reconcile()
            self.bot.exit_tick(self.client.quote())
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.bot.position())
            self.assertFalse(self.bot.orders.active())

        def test_46_process_lock_excludes_second_process(self):
            path=Path(self.tmp.name)/'test.lock'
            with path.open('a') as first, path.open('a') as second:
                acquire_process_lock(first)
                with self.assertRaises(SafetyError): acquire_process_lock(second)
            with path.open('a') as third:
                acquire_process_lock(third)
        def grid5_fixture(self, short=False):
            # Independent test-only limits: production risk settings are untouched.
            self.cfg.update(grid_max_layers=5,grid_spacings=[0.005,0.007,0.009,0.012,0.015],
                            grid_order_sizes=[1,2,3,4,5],size_unit='equity_fraction',
                            max_symbol_equity_pct=30,max_account_equity_pct=30,max_margin_equity_pct=0.9)
            self.client.m.update(tickSize='0.0001',stepSize='0.000001')
            self.bot.market=self.client.market()
            self.client.q={'bid':dec('99999'),'ask':dec('100001'),'mid':dec('100000')}
            first=self.entry(short)
            self.client.fill(first['order_id'],first['body']['quantity'],'100000')
            self.bot.reconcile()
            return first

        def test_47_grid5_long_short_price_paths_and_live_equity(self):
            paths={False:['99500.0000', '98803.5000', '97914.2685', '96739.2972', '95288.2077'],
                   True:['100500.0000', '101203.5000', '102114.3315', '103339.7035', '104889.7991']}
            # Restart each side from an independent exchange/journal fixture.
            for short,expected in paths.items():
                with self.subTest(short=short):
                    self.client=FakeClient(self.cfg)
                    self.path=Path(self.tmp.name)/('short.json' if short else 'long.json')
                    self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                    self.bot.recover()
                    self.grid5_fixture(short)
                    account=self.client.account
                    for layer,px in enumerate(expected,1):
                        # Changing account equity must be used by the next layer.
                        equity=dec(10000+layer*1000)
                        def snapshot(equity=equity):
                            row=account()
                            row['equity']=str(equity)
                            return row
                        self.client.account=snapshot
                        self.bot.reconcile()
                        self.bot.grid.tick(self.client.q)
                        rec=self.bot.orders.active({'G'})[0]
                        self.assertEqual(rec['layer'],layer)
                        self.assertEqual(dec(rec['body']['price']),dec(px))
                        self.assertEqual(rec['body']['timeInForce'],'ALO')
                        self.assertFalse(rec['body']['reduceOnly'])
                        risk_price=max(dec(px),self.client.q['ask'])
                        expected_qty=floor_step(equity*layer/risk_price,self.client.m['stepSize'])
                        self.assertEqual(dec(rec['body']['quantity']),expected_qty)
                        count=self.client.placed
                        self.bot.grid.tick(self.client.q)
                        self.assertEqual(self.client.placed,count)
                        self.client.fill(rec['order_id'],rec['body']['quantity'])
                        self.bot.reconcile()
                        self.assertEqual(dec(self.bot.state['managed']['last_fill_price']),dec(px))
                        # Move the quote to the last fill so mirrored resting orders remain valid.
                        self.client.q={'bid':dec(px)-1,'ask':dec(px)+1,'mid':dec(px)}
                    self.bot.grid.tick(self.client.q)
                    self.assertEqual(self.client.placed,6)
                    self.assertEqual(sorted(r['layer'] for r in self.bot.state['orders'].values()),list(range(6)))

        def test_48_partial_grid_and_canceled_partial_never_advance(self):
            self.filled_entry()
            self.bot.grid.tick(self.client.q)
            rec=self.bot.orders.active({'G'})[0]
            self.client.fill(rec['order_id'],dec(rec['body']['quantity'])/2)
            self.bot.reconcile()
            self.bot.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,2)
            self.bot.orders.cancel(self.bot.orders.active({'G'})[0])
            self.bot.reconcile()
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            restarted.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,2)
            self.assertFalse(restarted.orders.active({'G'}))

        def test_49_partial_first_entry_canceled_never_starts_grid(self):
            rec=self.entry()
            self.client.fill(rec['order_id'],'0.5')
            self.bot.reconcile()
            self.bot.orders.cancel(self.bot.orders.active({'E'})[0])
            self.bot.reconcile()
            self.bot.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,1)

        def test_50_grid5_restart_actual_fill_anchor(self):
            self.grid5_fixture()
            for layer in range(1,6):
                self.bot.grid.tick(self.client.q)
                rec=self.bot.orders.active({'G'})[0]
                actual=dec(rec['body']['price'])-dec('1.2345')
                self.client.fill(rec['order_id'],rec['body']['quantity'],actual)
                self.bot.reconcile()
                self.client.q={'bid':actual-1,'ask':actual+1,'mid':actual}
                # A valid durable management state preserves the original grid layer.
                self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                self.bot.recover()
                self.assertEqual(dec(self.bot.state['managed']['last_fill_price']),actual)
                self.assertEqual(self.bot.state['managed']['layers'],layer+1)
                if layer<5:
                    self.bot.grid.tick(self.client.q)
                    nxt=self.bot.orders.active({'G'})[0]
                    expected=bounded_price(self.bot.market,actual*(1-dec(self.cfg['grid_spacings'][layer])),'BUY')
                    self.assertEqual(dec(nxt['body']['price']),expected)
            count=self.client.placed
            self.bot.grid.tick(self.client.q)
            self.assertEqual(count,6)
            self.assertEqual(self.client.placed,count)

        def test_51_grid5_unknown_outcome_never_advances_or_resubmits(self):
            self.filled_entry()
            self.client.timeout_after_submit=True
            self.bot.grid.tick(self.client.q)
            self.bot.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,2)
            self.bot.reconcile()
            self.bot.grid.tick(self.client.q)
            self.assertEqual(self.client.placed,2)

        def test_52_grid5_config_validation_and_legacy_separation(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(grid_max_layers=5,grid_spacings=[0.005,0.007,0.009,0.012,0.015],
                       grid_order_sizes=[1,2,3,4,5],size_unit='equity_fraction',
                       max_symbol_equity_pct=20,max_account_equity_pct=20)
            path=Path(self.tmp.name)/'validation.json'
            def load(value):
                path.write_text(json.dumps(value))
                return load_config(path)
            self.assertEqual(load(cfg)['grid_max_layers'],5)
            for field,values in [('grid_spacings',[None,[],[0.01]*4,[0]*5,[1]*5,[-0.1]*5]),
                                 ('grid_order_sizes',[None,[],[1]*4,[0]*5,[-1]*5])]:
                for value in values:
                    with self.subTest(field=field,value=value):
                        invalid=copy.deepcopy(cfg); invalid[field]=value
                        with self.assertRaises(SafetyError): load(invalid)
            invalid=copy.deepcopy(cfg); del invalid['grid_spacings']
            with self.assertRaises(SafetyError): load(invalid)
            invalid=copy.deepcopy(cfg); invalid['grid_max_layers']=6
            with self.assertRaises(SafetyError): load(invalid)
            invalid=copy.deepcopy(cfg)
            invalid.update(max_symbol_equity_pct=3.5,max_account_equity_pct=3.5)
            with self.assertRaisesRegex(SafetyError,'max_symbol_equity_pct'): load(invalid)
            legacy=copy.deepcopy(cfg)
            legacy.update(grid_mode='legacy_dynamic',grid_max_layers=2,grid_order_sizes=[1,2])
            del legacy['grid_spacings']
            self.assertEqual(load(legacy)['grid_spacing'],cfg['grid_spacing'])
            legacy.update(tp_mode='legacy_layered',grid_max_layers=5,grid_order_sizes=[1,2,3,4,5],
                          take_profit_by_layer=[0.01]*3,trailing_drawdown_by_layer=[0]*3)
            with self.assertRaises(SafetyError): load(legacy)

        def test_53_rsi_live_and_dry_fetch_only_5m(self):
            for dry in (False,True):
                with self.subTest(dry=dry):
                    def candles(tf):
                        self.assertEqual(tf,'5m')
                        return bars(300,now=self.now)
                    with patch.object(self.client,'candles',side_effect=candles) as fetch, \
                         patch(__name__+'.calc_rsi',side_effect=[31,29]), \
                         patch(__name__+'.calc_ema_series',side_effect=AssertionError('EMA被调用')), \
                         patch(__name__+'.calc_adx',side_effect=AssertionError('ADX被调用')), \
                         patch('builtins.print'):
                        if dry:
                            self.client.rows.clear()
                            r=observe_once(self.client,self.cfg,Path(self.tmp.name)/'rsi-dry.json')
                            self.assertEqual(r['side'],'LONG')
                        else:
                            self.bot.tick()
                            self.assertEqual(self.bot.orders.active({'E'})[0]['body']['orderSide'],'BUY')
                        self.assertEqual([c.args[0] for c in fetch.call_args_list],['5m'])
                    self.assertEqual(self.client.placed,1)

        def test_54_closed_5m_only(self):
            rows=bars(300,now=self.now)
            current=dict(rows[-1],openTime=self.now*1000000,isFinal=False,close=99999)
            with patch(__name__+'.calc_rsi',side_effect=[31,29]) as calc:
                r=evaluate(None,rows+[current],self.cfg,now=self.now,account_known=True)
            self.assertEqual(r['side'],'LONG')
            self.assertEqual(r['bar'],self.now-300)
            self.assertEqual(calc.call_args_list[0].args,([x['close'] for x in rows],7))
            self.assertEqual(calc.call_args_list[1].args,([x['close'] for x in rows[:-1]],7))
            for invalid in (rows[:-1],rows+[rows[-1]],[],[dict(x,isFinal=False) for x in rows]):
                self.assertFalse(evaluate(None,invalid,self.cfg,now=self.now,account_known=True)['signal'])

        def test_55_real_rsi_reentry(self):
            for short in (False,True):
                rows=bars(300,now=self.now)
                prices=[1000-i for i in range(len(rows))]
                prices[-1]=prices[-2]+10
                if short:
                    prices=[2000-x for x in prices]
                for row,px in zip(rows,prices):
                    row.update(open=px,high=px+1,low=px-1,close=px)
                r=evaluate(None,rows,self.cfg,now=self.now,account_known=True)
                self.assertEqual(r['side'],'SHORT' if short else 'LONG')

        def test_56_restart_and_old_ledger_dedup(self):
            ledger=self.bot.state['ledger']
            self.assertTrue(self.signal(ledger=ledger)['signal'])
            self.bot.save()
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            self.assertFalse(self.signal(ledger=restarted.state['ledger'])['signal'])
            self.assertTrue(signal_seen(ledger,self.now-600))
            self.assertFalse(signal_seen(ledger,self.now))
            old=dict(last_signal_bar=self.now-900,last_signal_bar_5m=self.now-300,
                     last_signal_side='LONG',signal_time=self.now)
            self.assertTrue(signal_seen(old,self.now-300))
            self.assertFalse(signal_seen(old,self.now))
            old.pop('last_signal_bar_5m')
            self.assertTrue(signal_seen(old,self.now-900))
            self.assertFalse(signal_seen(old,self.now-300))
            old['last_signal_bar_5m']='invalid'
            self.assertFalse(self.signal(ledger=old)['signal'])

        def test_57_15m_not_required(self):
            with patch(__name__+'.calc_rsi',side_effect=[31,29]):
                r=evaluate(None,None,self.cfg,five=bars(300),now=self.now,account_known=True)
            self.assertEqual(r['side'],'LONG')

        def test_58_no_cross_no_order(self):
            for prev,cur in [(20,25),(31,32),(80,75),(69,68),(29,30),(71,70),(31,29),(69,71)]:
                with patch(__name__+'.calc_rsi',side_effect=[cur,prev]), patch('builtins.print'):
                    self.bot.tick()
                self.assertEqual(self.client.placed,0)
                self.assertFalse(self.bot.state['ledger'])

        def test_59_layered_tp_examples(self):
            long_prices=[86602,86602,86602,86430,86430,86258]
            short_prices=[85398,85398,85398,85570,85570,85742]
            for layer in range(6):
                with self.subTest(layer=layer):
                    self.bot.state['managed']['grid_layer']=layer
                    self.assertEqual(tp_pct_for_grid_layer(self.cfg,layer),
                                     dec([0.007,0.007,0.007,0.005,0.005,0.003][layer]))
                    self.assertEqual(self.bot.tp.target({'qty':'1','entry':'86000'}),dec(long_prices[layer]))
                    self.assertEqual(self.bot.tp.target({'qty':'-1','entry':'86000'}),dec(short_prices[layer]))

        def test_60_every_grid_fill_refreshes_whole_position_tp(self):
            for short in (False,True):
                with self.subTest(short=short):
                    self.client=FakeClient(self.cfg)
                    self.path=Path(self.tmp.name)/('tp-short.json' if short else 'tp-long.json')
                    self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                    self.bot.recover()
                    self.grid5_fixture(short)
                    self.cfg['take_profit_pct']=0.007
                    self.bot.tp.tick(self.client.q)
                    self.bot.reconcile()
                    for layer in range(1,6):
                        oldtp=self.bot.orders.active({'T'})[0]
                        self.bot.grid.tick(self.client.q)
                        grid=self.bot.orders.active({'G'})[0]
                        self.client.fill(grid['order_id'],grid['body']['quantity'])
                        self.bot.reconcile()
                        position=self.client.account()['positions']['BTC-USD']
                        expected=bounded_price(self.bot.market,dec(position['entry'])*
                                               (1+dec([0.007,0.007,0.007,0.005,0.005,0.003][layer])*(-1 if short else 1)),
                                               'BUY' if short else 'SELL')
                        self.bot.tp.tick(self.client.q)
                        self.assertTrue(self.bot.state['orders'][oldtp['body']['clientId']]['cancel_requested'])
                        self.bot.reconcile()
                        self.assertTrue(self.bot.state['orders'][oldtp['body']['clientId']]['terminal'])
                        self.bot.tp.tick(self.client.q)
                        tp=self.bot.orders.active({'T'})[0]
                        self.assertEqual(dec(tp['body']['price']),expected)
                        self.assertEqual(dec(tp['body']['quantity']),abs(dec(position['qty'])))
                        self.assertTrue(tp['body']['reduceOnly'])
                        self.assertEqual(tp['body']['orderSide'],'BUY' if short else 'SELL')
                        self.assertNotEqual(tp['order_id'],oldtp['order_id'])
                        self.bot.reconcile()
                        count=self.client.placed
                        self.bot.tp.tick(self.client.q)
                        self.assertEqual(self.client.placed,count)
                        last=dec(self.bot.state['managed']['last_fill_price'])
                        self.client.q={'bid':last-1,'ask':last+1,'mid':last}
                    # A partial TP fill must reduce exposure; the remainder flattens it.
                    tp=self.bot.orders.active({'T'})[0]
                    qty=abs(self.client.qty)
                    first=floor_step(qty/2,self.client.m['stepSize'])
                    self.client.fill(tp['order_id'],first)
                    self.bot.reconcile()
                    self.assertEqual(abs(self.client.qty),qty-first)
                    self.assertEqual(self.client.qty<0,short)
                    self.client.fill(tp['order_id'],qty-first)
                    self.bot.reconcile()
                    self.assertEqual(self.client.qty,0)
                    self.bot.exit_tick(self.client.q)
                    self.assertEqual(self.bot.state['state'],'WAIT')
                    self.assertFalse(self.bot.orders.active())

        def notification_capture(self, bot=None):
            bot=self.bot if bot is None else bot
            messages=[]
            capture=patch.object(bot.notifications,'_enqueue',side_effect=messages.append)
            capture.start()
            self.addCleanup(capture.stop)
            return messages

        def telegram_test_config(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.update(telegram_enabled=True,telegram_bot_token='123:test-secret',telegram_chat_id='test-chat')
            return cfg

        def test_61_telegram_startup_once_no_signal_or_order_ack(self):
            messages=self.notification_capture()
            self.bot.notifications.safe('startup')
            self.bot.notifications.safe('startup')
            self.assertEqual(len(messages),1)
            self.assertIn('机器人启动',messages[0])
            self.assertTrue(self.signal()['signal'])
            rec=self.entry()
            self.bot.reconcile()
            self.assertEqual(len(messages),1)
            self.client.fill(rec['order_id'],'0.4')
            self.bot.reconcile()
            self.bot.reconcile()
            self.assertEqual(len(messages),1)
            self.client.fill(rec['order_id'],'0.6')
            self.bot.reconcile()
            self.bot.reconcile()
            self.assertEqual(len(messages),2)
            self.assertIn('首仓成交',messages[1])
            persisted=json.loads(self.path.read_text())
            self.assertIn(self.bot.state['cycle']+':E:0',persisted['telegram']['claimed'])

        def test_62_telegram_all_grid_layers_rest_ws_and_tp_close(self):
            messages=self.notification_capture()
            self.grid5_fixture()
            self.assertEqual(len(messages),1)
            self.bot.tp.tick(self.client.q)
            self.bot.reconcile()
            self.assertEqual(len(messages),1)
            for layer in range(1,6):
                self.bot.grid.tick(self.client.q)
                self.bot.reconcile()
                grid=self.bot.orders.active({'G'})[0]
                self.assertEqual(len(messages),layer)
                half=floor_step(dec(grid['body']['quantity'])/2,self.client.m['stepSize'])
                self.client.fill(grid['order_id'],half)
                self.bot.reconcile()
                self.assertEqual(len(messages),layer)
                self.client.fill(grid['order_id'],dec(grid['body']['quantity'])-half)
                event=self.client.order(grid['order_id'])
                with patch.object(self.bot.stream,'find',side_effect=lambda cid,oid: event if oid==grid['order_id'] else None):
                    self.bot.reconcile()
                    self.bot.reconcile()
                self.bot.reconcile()
                self.assertEqual(len(messages),layer+1)
                self.assertIn(f'层级：G{layer} / G5',messages[-1])
                self.assertIn('最新整仓均价：'+self.bot.position()['entry'],messages[-1])
                self.bot.tp.tick(self.client.q)
                self.bot.reconcile()
                self.bot.tp.tick(self.client.q)
                self.bot.reconcile()
                self.assertEqual(len(messages),layer+1)
                last=dec(self.bot.state['managed']['last_fill_price'])
                self.client.q={'bid':last-1,'ask':last+1,'mid':last}
            tp=self.bot.orders.active({'T'})[0]
            self.client.fill(tp['order_id'],tp['body']['quantity'])
            self.bot.reconcile()
            self.assertEqual(len(messages),6)  # Still EXITING, not WAIT.
            self.bot.exit_tick(self.client.q)
            self.assertEqual(len(messages),7)
            self.assertIn('平仓类型：TP',messages[-1])
            self.assertIn('本轮最终状态：WAIT',messages[-1])
            self.bot.reconcile()
            self.bot.notifications.safe('finished')
            self.assertEqual(len(messages),7)
            self.assertFalse(self.bot.position())

        def test_63_telegram_restart_and_old_journal_silent(self):
            messages=self.notification_capture()
            self.filled_entry()
            self.bot.grid.tick(self.client.q)
            grid=self.bot.orders.active({'G'})[0]
            self.client.fill(grid['order_id'],grid['body']['quantity'])
            self.bot.reconcile()
            self.assertEqual(len(messages),2)
            for recovery in ('saved','old-state','exchange-history'):
                with self.subTest(recovery=recovery):
                    if recovery=='old-state':
                        state=json.loads(self.path.read_text()); state.pop('telegram',None)
                        atomic_json(self.path,state)
                    elif recovery=='exchange-history':
                        self.path.unlink()
                    restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                    captured=self.notification_capture(restarted)
                    restarted.recover()
                    restarted.reconcile()
                    self.assertEqual(captured,[])
                    restarted.notifications.safe('startup')
                    self.assertEqual(len(captured),1)
                    self.assertIn('Arcus双币种对冲机器人启动\n交易对：BTC-USD',captured[0])
                    if recovery=='exchange-history':
                        self.assertIn('接管状态：已自动接管',captured[0])
                    self.assertRegex(captured[0],r'时间：\d{4}-\d{2}-\d{2} \d{2}:\d{2}\Z')

        def test_64_telegram_short_sl_only_after_flat_and_wait(self):
            messages=self.notification_capture()
            self.filled_entry(True)
            self.assertIn('方向：SHORT',messages[0])
            self.bot.begin_exit('价格止损')
            self.bot.exit_tick(self.client.q)
            close=self.bot.orders.active({'X'})[0]
            self.bot.reconcile()
            self.assertEqual(len(messages),1)
            self.client.fill(close['order_id'],close['body']['quantity'])
            self.bot.reconcile()
            self.assertEqual(len(messages),1)
            self.bot.exit_tick(self.client.q)
            self.assertEqual(len(messages),2)
            self.assertIn('平仓类型：SL',messages[-1])
            self.assertIn('方向：SHORT',messages[-1])

        def test_65_telegram_disabled_missing_fields_and_env_precedence(self):
            cfg=self.telegram_test_config()
            with patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'','ARCUS_TELEGRAM_CHAT_ID':''}),\
                 patch(__name__+'.requests.post') as post:
                for fields in ({'telegram_enabled':False},{'telegram_bot_token':''},{'telegram_chat_id':''}):
                    off=dict(cfg,**fields)
                    self.assertFalse(send_telegram('test',off))
                    notice=TelegramNotifications(cfg=off)
                    notice.safe('startup','WAIT')
                    self.assertIsNone(notice.worker)
                    self.bot.cfg.update(fields)
                    self.bot.tick()  # Missing notification config never blocks trading.
                post.assert_not_called()
                self.assertEqual(telegram_credentials(cfg),('123:test-secret','test-chat'))
            with patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'env-token','ARCUS_TELEGRAM_CHAT_ID':'env-chat'}):
                self.assertEqual(telegram_credentials(cfg),('env-token','env-chat'))
                self.assertEqual(telegram_credentials(dict(cfg,telegram_enabled=False)),('',''))

        def test_66_telegram_errors_redacted_single_attempt(self):
            from unittest.mock import Mock
            cfg=self.telegram_test_config()
            for outcome in ('timeout','network',429,500,'api-error','bad-json','success'):
                with self.subTest(outcome=outcome),\
                     patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'','ARCUS_TELEGRAM_CHAT_ID':''}),\
                     patch(__name__+'.requests.post') as post, patch(__name__+'.log') as logged:
                    if outcome in ('timeout','network'):
                        post.side_effect=(requests.Timeout if outcome=='timeout' else requests.ConnectionError)('123:test-secret URL')
                    else:
                        response=Mock(status_code=outcome if isinstance(outcome,int) else 200)
                        response.json.return_value={'ok':outcome=='success','description':'123:test-secret'}
                        if outcome=='bad-json': response.json.side_effect=ValueError('123:test-secret')
                        post.return_value=response
                    self.assertEqual(send_telegram('test',cfg),outcome=='success')
                    post.assert_called_once()
                    self.assertEqual(post.call_args.kwargs['timeout'],(3,5))
                    self.assertFalse(post.call_args.kwargs['allow_redirects'])
                    self.assertNotIn('test-secret',str(logged.call_args_list))

        def test_67_telegram_worker_cannot_block_trading(self):
            self.cfg.update(self.telegram_test_config())
            entered=threading.Event(); release=threading.Event(); completed=threading.Event()
            def stalled(*args,**kwargs):
                entered.set()
                release.wait(3)
                completed.set()
                raise requests.Timeout('secret')
            with patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'','ARCUS_TELEGRAM_CHAT_ID':''}),\
                 patch(__name__+'.requests.post',side_effect=stalled):
                try:
                    self.bot.notifications.safe('startup')
                    self.assertTrue(entered.wait(1))
                    self.filled_entry()
                    self.bot.tp.tick(self.client.q)
                    self.bot.reconcile()
                    self.assertEqual(len(self.bot.orders.active({'T'})),1)
                    self.assertFalse(completed.is_set())  # Trading completed while HTTP is stalled.
                finally:
                    release.set()
                    self.bot.notifications.messages.join()  # Tests only; trading never waits.
            self.assertFalse(self.bot.notifications.disabled)

        def test_68_telegram_failure_persists_claim_before_enqueue(self):
            captured=[]
            def failed(message):
                persisted=json.loads(self.path.read_text())
                self.assertIn(self.bot.state['cycle']+':E:0',persisted['telegram']['claimed'])
                captured.append(message)
                raise RuntimeError('simulated worker startup failure')
            with patch.object(self.bot.notifications,'_enqueue',side_effect=failed):
                self.filled_entry()
                self.bot.reconcile()
                self.bot.tp.tick(self.client.q)
            self.assertEqual(len(captured),1)
            self.assertEqual(len(self.bot.orders.active({'T'})),1)
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            messages=self.notification_capture(restarted)
            restarted.recover(); restarted.reconcile()
            self.assertEqual(messages,[])

        def test_69_telegram_queue_full_drops_without_retry(self):
            notice=TelegramNotifications(cfg=self.telegram_test_config())
            notice.worker=object()  # Hold the worker off; fill bounded queue deterministically.
            with patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'','ARCUS_TELEGRAM_CHAT_ID':''}),\
                 patch(__name__+'.requests.post') as post:
                for _ in range(65): notice.safe('_enqueue','test')
                self.assertEqual(notice.messages.qsize(),64)
                self.assertFalse(notice.disabled)
                post.assert_not_called()

        def test_70_telegram_429_500_worker_does_not_retry_orders(self):
            from unittest.mock import Mock
            for status in (429,500):
                with self.subTest(status=status):
                    cfg=self.telegram_test_config()
                    client=FakeClient(cfg)
                    bot=Bot(cfg,client,Feed(),Path(self.tmp.name)/f'telegram-{status}.json',emit=lambda *a,**k:None)
                    bot.recover()
                    response=Mock(status_code=status)
                    with patch.dict(os.environ,{'ARCUS_TELEGRAM_BOT_TOKEN':'','ARCUS_TELEGRAM_CHAT_ID':''}),\
                         patch(__name__+'.requests.post',return_value=response) as post:
                        bot.notifications.safe('startup')
                        bot.state['cycle']=f'{self.now:08x}abcdef'
                        rec=bot.orders.submit('E',0,'BUY',dec(1),dec(99))
                        client.fill(rec['order_id'],'1')
                        bot.reconcile()
                        bot.tp.tick(client.q)
                        bot.reconcile()
                        bot.notifications.messages.join()
                        self.assertEqual(post.call_count,2)
                        self.assertEqual(client.placed,2)  # One entry and one TP; no retry.
                        self.assertFalse(bot.notifications.disabled)

        def test_71_telegram_bad_journal_does_not_block_recovery(self):
            self.bot.state['telegram']={'version':99,'claimed':None}
            self.bot.save()
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            self.assertTrue(restarted.notifications.disabled)
            restarted.state['cycle']=f'{self.now:08x}abcdef'
            rec=restarted.orders.submit('E',0,'BUY',dec(1),dec(99))
            self.client.fill(rec['order_id'],'1')
            restarted.reconcile()
            restarted.tp.tick(self.client.q)
            self.assertEqual(len(restarted.orders.active({'T'})),1)

        def external_position(self, short=False, entry='86000', qty='0.05'):
            self.cfg.update(size_unit='equity_fraction',first_order_size=0.9,grid_max_layers=5,
                            grid_order_sizes=[1,2,3,4,5],grid_spacings=[0.005,0.007,0.009,0.012,0.015],
                            take_profit_pct=0.007)
            self.client=FakeClient(self.cfg)
            self.client.qty=dec(qty)*(-1 if short else 1)
            self.client.entry=dec(entry)
            self.client.q={'bid':dec(entry)-1,'ask':dec(entry)+1,'mid':dec(entry)}
            self.path=Path(self.tmp.name)/('external-short.json' if short else 'external-long.json')
            self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            return self.bot

        def test_72_external_long_short_g0_without_history(self):
            for short in (False,True):
                with self.subTest(short=short):
                    b=self.external_position(short)
                    messages=self.notification_capture()
                    with patch.object(self.client,'order_history',side_effect=AssertionError('无需用订单历史判断仓位来源')):
                        b.recover()
                    self.assertEqual(b.state['state'],'GRID_SHORT' if short else 'GRID_LONG')
                    self.assertEqual(b.state['managed']['grid_layer'],0)
                    self.assertEqual(dec(b.state['managed']['last_fill_price']),dec(86000))
                    self.assertEqual(dec(b.state['base_qty']),self.client.qty)
                    self.assertEqual(b.state['orders'],{})
                    self.assertEqual(messages,[])
                    b.notifications.safe('startup')
                    self.assertEqual(len(messages),1)
                    self.assertIn('已自动接管',messages[0])
                    with patch(__name__+'.evaluate',side_effect=AssertionError('有仓位不运行D1')),\
                         patch.object(b.entry,'tick',side_effect=AssertionError('有仓位不运行D2')),\
                         patch.object(self.client,'candles',side_effect=AssertionError('不读取RSI行情')):
                        b.tick()
                        b.tick()
                    tp=b.orders.active({'T'})[0]
                    self.assertEqual(dec(tp['body']['price']),dec(85398 if short else 86602))
                    self.assertTrue(tp['body']['reduceOnly'])
                    self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
                    grid=b.orders.active({'G'})[0]
                    self.assertEqual(grid['layer'],1)
                    self.assertEqual(dec(grid['body']['price']),dec(86430 if short else 85570))
                    with self.assertRaises(SafetyError): b.orders.submit('E',0,'BUY',dec('0.01'),dec(85000))
                    self.assertEqual(len(messages),1)

        def test_73_adopted_all_layers_restart_tp_and_telegram(self):
            for short in (False,True):
                with self.subTest(short=short):
                    b=self.external_position(short)
                    messages=self.notification_capture()
                    b.recover()
                    cycle=b.state['cycle']
                    b.notifications.safe('startup')
                    b.tp.tick(self.client.q); b.reconcile()
                    for layer in range(1,6):
                        previous=dec(b.state['managed']['last_fill_price'])
                        b.grid.tick(self.client.q)
                        grid=b.orders.active({'G'})[0]
                        expected=bounded_price(b.market,previous*(1+dec(self.cfg['grid_spacings'][layer-1])*(-1 if not short else 1)),
                                               'SELL' if short else 'BUY')
                        self.assertEqual(dec(grid['body']['price']),expected)
                        self.assertEqual(grid['layer'],layer)
                        self.assertEqual(grid['body']['timeInForce'],'ALO')
                        count=self.client.placed
                        b.grid.tick(self.client.q)
                        self.assertEqual(self.client.placed,count)
                        half=floor_step(dec(grid['body']['quantity'])/2,self.client.m['stepSize'])
                        self.client.fill(grid['order_id'],half)
                        b.reconcile()
                        self.assertEqual(b.state['managed']['grid_layer'],layer-1)
                        b.grid.tick(self.client.q)
                        self.assertEqual(self.client.placed,count)
                        actual=expected+(dec('0.1') if short else dec('-0.1'))
                        self.client.fill(grid['order_id'],dec(grid['body']['quantity'])-half,actual)
                        b.reconcile()
                        actual=dec(self.client.order(grid['order_id'])['avgFillPrice'])
                        self.assertEqual(b.state['managed']['grid_layer'],layer)
                        self.assertEqual(dec(b.state['managed']['last_fill_price']),actual)
                        self.assertEqual(sum(f'层级：G{layer} / G5' in m for m in messages),1)
                        b.tp.tick(self.client.q); b.reconcile()
                        b.tp.tick(self.client.q); b.reconcile()
                        tp=b.orders.active({'T'})[0]
                        pos=self.client.account()['positions']['BTC-USD']
                        self.assertEqual(dec(tp['body']['price']),bounded_price(b.market,dec(pos['entry'])*
                                         (1+dec([0.007,0.007,0.007,0.005,0.005,0.003][layer])*(-1 if short else 1)),'BUY' if short else 'SELL'))
                        self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
                        self.assertTrue(tp['body']['reduceOnly'])
                        last=actual
                        self.client.q={'bid':last-1,'ask':last+1,'mid':last}
                        if layer in (1,3,5):
                            b=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                            cap=patch.object(b.notifications,'_enqueue',side_effect=messages.append)
                            cap.start(); self.addCleanup(cap.stop)
                            b.recover()
                            self.assertEqual(b.state['cycle'],cycle)
                            self.assertEqual(b.state['managed']['grid_layer'],layer)
                            self.assertEqual(dec(b.state['managed']['last_fill_price']),last)
                    count=self.client.placed
                    b.grid.tick(self.client.q)
                    self.assertEqual(self.client.placed,count)
                    self.assertFalse(any('首仓成交' in m for m in messages))
                    tp=b.orders.active({'T'})[0]
                    self.client.fill(tp['order_id'],tp['body']['quantity'])
                    b.reconcile(); b.exit_tick(self.client.q)
                    self.assertEqual(b.state['state'],'WAIT')
                    self.assertEqual(b.state['managed'],{})
                    self.assertFalse(b.orders.active())
                    self.assertEqual(sum('本轮交易结束' in m for m in messages),1)
                    self.client.t+=self.cfg['cooldown_seconds']+1
                    def current_candles(tf):
                        step=300 if tf=='5m' else 900
                        rows=bars(step,now=self.now)
                        offset=int(self.client.now()//step)*step-self.now
                        return [dict(r,openTime=r['openTime']+offset*1000000) for r in rows]
                    with patch(__name__+'.calc_rsi',side_effect=[31,29]),\
                         patch.object(self.client,'candles',side_effect=current_candles), patch('builtins.print'):
                        b.tick()
                    self.assertEqual(len(b.orders.active({'E'})),1)

        def test_74_existing_tp_keep_replace_and_multiple(self):
            for mode in ('correct','price','quantity','wrong-side','multiple','no-client-id','partial'):
                with self.subTest(mode=mode):
                    b=self.external_position()
                    if self.path.exists(): self.path.unlink()
                    b=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                    self.bot=b
                    body={'clientId':None if mode=='no-client-id' else 'manual-protection',
                          'orderSide':'BUY' if mode=='wrong-side' else 'SELL','quantity':'0.02' if mode=='quantity' else '0.05',
                          'price':'87000' if mode=='price' else '86602','timeInForce':'GTT','reduceOnly':True}
                    ack=self.client.place(body,self.client.m)
                    if mode=='multiple':
                        self.client.place(dict(body,clientId='second-protection'),self.client.m)
                    if mode=='partial':
                        self.client.fill(ack['orderId'],'0.01')
                    count=self.client.placed
                    b.recover()
                    b.tp.tick(self.client.q)
                    if mode in ('correct','no-client-id','partial'):
                        self.assertEqual(self.client.placed,count)
                        self.assertEqual(self.client.canceled,0)
                        self.assertEqual(b.orders.active({'T'})[0]['order_id'],ack['orderId'])
                    else:
                        self.assertGreater(self.client.canceled,0)
                        self.assertEqual(self.client.placed,count)
                        b.reconcile(); b.tp.tick(self.client.q); b.reconcile()
                        tp=b.orders.active({'T'})[0]
                        self.assertEqual(tp['body']['orderSide'],'SELL')
                        self.assertEqual(dec(tp['body']['price']),dec(86602))
                        self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
                        self.assertTrue(tp['body']['reduceOnly'])

        def test_75_external_flat_cleanup_and_live_detection(self):
            # A position opened manually while the process runs is also adopted.
            self.client.qty=dec('1'); self.client.entry=dec('100'); self.client.seq+=1
            messages=self.notification_capture()
            self.bot.reconcile()
            self.assertEqual(self.bot.state['managed']['grid_layer'],0)
            self.assertEqual(messages,[])
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            self.bot.grid.tick(self.client.q); self.bot.reconcile()
            self.client.qty=dec(0); self.client.entry=dec(0); self.client.seq+=1
            self.bot.tick()
            self.bot.tick()
            self.bot.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertEqual(self.bot.state['managed'],{})
            self.assertFalse(self.bot.orders.active())
            self.assertEqual(sum('本轮交易结束' in m for m in messages),1)
            self.assertIn('平仓类型：其他',messages[-1])

        def test_76_takeover_does_not_override_unknown_or_foreign_exposure(self):
            b=self.external_position()
            self.client.place({'clientId':'manual-buy','orderSide':'BUY','quantity':'0.01','price':'85000',
                               'timeInForce':'ALO','reduceOnly':False},self.client.m)
            with self.assertRaisesRegex(SafetyError,'未登记挂单'): b.recover()
            self.assertEqual(b.state['managed']['grid_layer'],0)
            self.assertEqual(self.client.placed,1)
            # Original unknown-order guard still blocks all new intents.
            self.client.rows.clear()
            b.recover()
            self.client.timeout_after_submit=True
            b.grid.tick(self.client.q)
            self.client.rows.clear()
            with self.assertRaises(SafetyError): b.reconcile()
            count=self.client.placed
            with self.assertRaises(SafetyError): b.orders.submit('G',2,'BUY',dec('0.01'),dec(84000))
            self.assertEqual(self.client.placed,count)

        def test_77_takeover_saved_unregistered_and_changed_position(self):
            # Migrate the old "needs confirmation" state without guessing old layers.
            self.bot.state.update(cycle='6b49d200abcdef',base_qty='1',known_qty='1',
                                  recovery_required='NEED_CONFIRMATION: old external position')
            self.bot.state['managed']={'layers':0,'last_fill_price':'100'}
            self.bot.save()
            self.client.qty=dec(1); self.client.entry=dec(100)
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            self.assertFalse(restarted.state['recovery_required'])
            first_cycle=restarted.state['cycle']
            restarted.reconcile()
            self.assertEqual(first_cycle,restarted.state['cycle'])
            self.client.qty=dec('-2'); self.client.entry=dec(105); self.client.seq+=1
            restarted.reconcile()
            self.assertEqual(restarted.state['state'],'GRID_SHORT')
            self.assertEqual(restarted.state['managed']['grid_layer'],0)
            self.assertEqual(dec(restarted.state['managed']['last_fill_price']),dec(105))
            self.assertNotEqual(restarted.state['cycle'],first_cycle)

        def halted_adoption(self, short=False):
            b=self.external_position(short)
            day=datetime.fromtimestamp(self.client.now(),timezone.utc).date().isoformat()
            # A same-day halt persisted BEFORE the position is adopted.
            b.state['daily']={'day':day,'start_equity':'10000','start_deposits':'10000',
                              'peak':'10000','halted':True}
            b.save()
            b.recover()
            return b

        def test_78_prior_halt_adopts_long_short_without_x(self):
            for short in (False,True):
                with self.subTest(short=short):
                    b=self.halted_adoption(short)
                    self.assertTrue(b.state['daily']['halted'])
                    self.assertEqual(b.state['managed']['grid_layer'],0)
                    self.assertEqual(b.state['managed']['layers'],1)
                    self.assertEqual(dec(b.state['managed']['last_fill_price']),dec(86000))
                    self.assertEqual(dec(b.state['managed']['position_entry']),dec(86000))
                    with patch.object(b,'begin_exit',wraps=b.begin_exit) as exit_call,\
                         patch(__name__+'.evaluate',side_effect=AssertionError('有仓位不得进入D1')),\
                         patch.object(b.entry,'tick',side_effect=AssertionError('有仓位不得进入D2')):
                        b.tick(); b.tick()
                        exit_call.assert_not_called()
                    self.assertEqual(b.state['state'],'GRID_SHORT' if short else 'GRID_LONG')
                    self.assertFalse(b.state['exiting'])
                    self.assertEqual(b.state['exit_reason'],'')
                    self.assertEqual(b.state['recovery_required'],'')
                    self.assertFalse(any(r['role'] in ('E','X') for r in b.state['orders'].values()))
                    tp=b.orders.active({'T'})[0]
                    grid=b.orders.active({'G'})[0]
                    self.assertEqual(dec(tp['body']['price']),dec(85398 if short else 86602))
                    self.assertTrue(tp['body']['reduceOnly'])
                    self.assertEqual(dec(grid['body']['price']),dec(86430 if short else 85570))
                    self.assertEqual(grid['layer'],1)
                    self.assertTrue(b.state['daily']['halted'])

        def test_79_halted_adoption_full_cycle_restart_and_next_entry(self):
            for short in (False,True):
                with self.subTest(short=short):
                    b=self.halted_adoption(short)
                    messages=self.notification_capture()
                    cycle=b.state['cycle']
                    b.tick(); b.tick()
                    for layer in range(1,6):
                        grid=b.orders.active({'G'})[0]
                        self.assertEqual(grid['layer'],layer)
                        oldtp=b.orders.active({'T'})[0]['order_id']
                        self.client.fill(grid['order_id'],grid['body']['quantity'])
                        last=dec(self.client.order(grid['order_id'])['avgFillPrice'])
                        self.client.q={'bid':last-1,'ask':last+1,'mid':last}
                        # Normal main-loop sequence: reconcile, cancel old TP,
                        # confirm cancellation, replace TP, then next grid.
                        b.tick(); b.tick(); b.tick()
                        self.assertFalse(b.state['exiting'])
                        self.assertTrue(b.state['daily']['halted'])
                        self.assertEqual(b.state['managed']['grid_layer'],layer)
                        self.assertEqual(dec(b.state['managed']['last_fill_price']),last)
                        tp=b.orders.active({'T'})[0]
                        self.assertNotEqual(tp['order_id'],oldtp)
                        pos=self.client.account()['positions']['BTC-USD']
                        self.assertEqual(dec(tp['body']['price']),bounded_price(b.market,
                            dec(pos['entry'])*(1+dec([0.007,0.007,0.007,0.005,0.005,0.003][layer])*(-1 if short else 1)),'BUY' if short else 'SELL'))
                        self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
                        self.assertTrue(tp['body']['reduceOnly'])
                        self.assertFalse(any(r['role']=='X' for r in b.state['orders'].values()))
                        if layer in (2,4):
                            b=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                            cap=patch.object(b.notifications,'_enqueue',side_effect=messages.append)
                            cap.start(); self.addCleanup(cap.stop)
                            b.recover(); b.tick()
                            self.assertEqual(b.state['cycle'],cycle)
                            self.assertEqual(b.state['managed']['grid_layer'],layer)
                            self.assertEqual(dec(b.state['managed']['last_fill_price']),last)
                            self.assertEqual(b.orders.active({'G'})[0]['layer'],layer+1)
                    self.assertFalse(b.orders.active({'G'}))
                    self.assertFalse(any(r['role']=='G' and r['layer']>5 for r in b.state['orders'].values()))
                    self.assertFalse(any('首仓成交' in m for m in messages))
                    for layer in range(1,6):
                        self.assertEqual(sum(f'层级：G{layer} / G5' in m for m in messages),1)
                    tp=b.orders.active({'T'})[0]
                    self.client.fill(tp['order_id'],tp['body']['quantity'])
                    b.tick()
                    self.assertEqual(b.state['state'],'WAIT')
                    self.assertEqual(b.state['managed'],{})
                    self.assertFalse(b.position())
                    self.assertEqual(sum('本轮交易结束' in m for m in messages),1)
                    # The old daily halt remains intact and still prevents a new E.
                    self.client.t+=self.cfg['cooldown_seconds']+1
                    def candles(tf):
                        step=300 if tf=='5m' else 900
                        offset=int(self.client.now()//step)*step-self.now
                        return [dict(r,openTime=r['openTime']+offset*1000000) for r in bars(step,now=self.now)]
                    with patch.object(self.client,'candles',side_effect=candles),\
                         patch(__name__+'.calc_rsi',side_effect=[31,29]), patch('builtins.print'):
                        b.tick()
                    self.assertTrue(b.state['daily']['halted'])
                    self.assertFalse(b.orders.active({'E'}))
                    # Existing UTC daily reset plus completed cooldown permits next cycle.
                    self.client.t+=86400
                    with patch.object(self.client,'candles',side_effect=candles),\
                         patch(__name__+'.calc_rsi',side_effect=[31,29]), patch('builtins.print'):
                        b.tick()
                    self.assertFalse(b.state['daily']['halted'])
                    self.assertEqual(len(b.orders.active({'E'})),1)

        def test_80_adopted_price_stop_remains_active_when_daily_halted(self):
            for short in (False,True):
                with self.subTest(short=short):
                    b=self.halted_adoption(short)
                    mid=dec(86000)*(1+dec(self.cfg['stop_loss_pct'])+dec('0.01') if short
                                    else 1-dec(self.cfg['stop_loss_pct'])-dec('0.01'))
                    self.client.q={'bid':mid-1,'ask':mid+1,'mid':mid}
                    b.tick()
                    self.assertTrue(b.state['exiting'])
                    self.assertEqual(b.state['exit_reason'],'价格止损')
                    close=b.orders.active({'X'})[0]
                    self.assertTrue(close['body']['reduceOnly'])
                    self.assertEqual(close['body']['orderSide'],'BUY' if short else 'SELL')

        def test_81_nonadopted_daily_risk_and_other_guards_unchanged(self):
            self.filled_entry()
            self.bot.update_daily()
            self.bot.state['daily']['halted']=True
            self.bot.tick()
            self.assertEqual(self.bot.state['exit_reason'],'日内亏损限制')
            self.assertEqual(len(self.bot.orders.active({'X'})),1)
            # Adoption bypasses only this daily flag, never spread/leverage/recovery guards.
            b=self.halted_adoption()
            with self.assertRaises(SafetyError):
                b.check_open_risk({'bid':dec(80000),'ask':dec(92000),'mid':dec(86000)})
            with patch.object(self.client,'verify_leverage',side_effect=SafetyError('杠杆不符')):
                with self.assertRaises(SafetyError): b.check_open_risk(self.client.q)
            b.state['recovery_required']='订单状态待确认'
            with self.assertRaises(SafetyError): b.check_open_risk(self.client.q)

        def test_82_rsi_30_70_boundaries_and_real_entry_path(self):
            cases=[(30,30.1,'LONG'),(29,31,'LONG'),(29,30,''),(31,29,''),
                   (70,69.9,'SHORT'),(71,69,'SHORT'),(71,70,''),(69,71,'')]
            for index,(prev,cur,side) in enumerate(cases):
                with self.subTest(case=index):
                    result=self.signal(prev=prev,cur=cur)
                    self.assertEqual(result['side'],side)
                    message=format_log(self.cfg['symbol'],result,self.cfg)
                    self.assertIn('5M回升穿过30=',message)
                    self.assertIn('5M回落穿过70=',message)
                    self.assertNotIn('15M',message)
                    client=FakeClient(self.cfg)
                    bot=Bot(self.cfg,client,Feed(),Path(self.tmp.name)/f'rsi-boundary-{index}.json',emit=lambda *a,**k:None)
                    bot.recover()
                    with patch(__name__+'.calc_rsi',side_effect=[cur,prev]), patch('builtins.print'):
                        bot.tick()
                    self.assertEqual(client.placed,1 if side else 0)
                    if side:
                        order=bot.orders.active({'E'})[0]
                        self.assertEqual(order['body']['orderSide'],'BUY' if side=='LONG' else 'SELL')
                        self.assertEqual(order['body']['timeInForce'],'ALO')

        def test_83_rsi_threshold_defaults_and_config_validation(self):
            cfg=copy.deepcopy(self.cfg)
            cfg.pop('rsi_long_threshold',None)
            cfg.pop('rsi_short_threshold',None)
            with patch.dict(self.cfg,cfg,clear=True):
                self.assertEqual(self.signal(prev=30,cur=31)['side'],'LONG')
                self.assertEqual(self.signal(prev=70,cur=69)['side'],'SHORT')
            for field,value in [('rsi_long_threshold',0),('rsi_short_threshold',100),
                                ('rsi_long_threshold',True),('rsi_short_threshold','70'),
                                ('rsi_long_threshold',78),('entry_timeframe','15m')]:
                with self.subTest(field=field,value=value):
                    bad=copy.deepcopy(self.cfg); bad[field]=value
                    with self.assertRaises(ValueError): validate_config(bad)

        def test_84_terminal_grid_fill_and_tp_updates_no_duplicates(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            self.bot.grid.tick(self.client.q); self.bot.reconcile()
            grid=self.bot.orders.active({'G'})[0]
            with patch(__name__+'.log') as output:
                self.client.fill(grid['order_id'],'0.4')
                self.bot.reconcile(); self.bot.reconcile()
                self.client.fill(grid['order_id'],'0.6')
                self.bot.reconcile(); self.bot.reconcile()
                self.bot.tp.tick(self.client.q)
                self.bot.tp.tick(self.client.q)  # Waiting for cancel confirmation, no duplicate log.
                self.bot.reconcile()
                self.bot.tp.tick(self.client.q)
                self.bot.reconcile(); self.bot.reconcile()
                kinds=[c.args[0] for c in output.call_args_list]
                self.assertEqual(kinds.count('GRID_PARTIAL_FILL'),1)
                self.assertEqual(kinds.count('GRID_FILLED'),1)
                self.assertEqual(kinds.count('TP_CANCEL_REQUESTED'),1)
                self.assertEqual(kinds.count('TP_SUBMITTED'),1)
                fill=next(c.kwargs for c in output.call_args_list if c.args[0]=='GRID_FILLED')
                self.assertEqual(fill['层级'],'G1')
                self.assertEqual(fill['最新整仓均价'],self.bot.position()['entry'])
                self.assertEqual(dec(fill['最新整仓数量']),dec('2'))
                tp=next(c.kwargs for c in output.call_args_list if c.args[0]=='TP_SUBMITTED')
                self.assertTrue(tp['reduceOnly'])
                self.assertEqual(dec(tp['TP数量']),dec('2'))
                statuses=[c.kwargs['状态'] for c in output.call_args_list if c.args[0]=='TP_STATUS']
                self.assertEqual(statuses,['CANCELED','OPEN'])
                output.reset_mock()
                restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                restarted.recover(); restarted.reconcile()
                output.assert_not_called()

        def test_85_terminal_output_failure_does_not_change_orders(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.q); self.bot.reconcile()
            self.bot.grid.tick(self.client.q); self.bot.reconcile()
            grid=self.bot.orders.active({'G'})[0]
            with patch(__name__+'.log',side_effect=OSError('console unavailable')):
                self.client.fill(grid['order_id'],grid['body']['quantity'])
                self.bot.reconcile()
                self.bot.tp.tick(self.client.q); self.bot.reconcile()
                self.bot.tp.tick(self.client.q); self.bot.reconcile()
            tp=self.bot.orders.active({'T'})[0]
            self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
            self.assertEqual(self.bot.state['state'],'GRID_LONG')
            self.assertTrue(tp['body']['reduceOnly'])

        def test_86_tp_tiers_partial_fill_switch_and_restart(self):
            for short in (False,True):
                with self.subTest(short=short), patch(__name__+'.log'):
                    self.client=FakeClient(self.cfg)
                    self.path=Path(self.tmp.name)/('tier-short.json' if short else 'tier-long.json')
                    self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                    self.bot.recover()
                    self.grid5_fixture(short)
                    self.bot.tp.tick(self.client.q); self.bot.reconcile()
                    rates=[dec('0.007'),dec('0.007'),dec('0.007'),dec('0.005'),dec('0.005'),dec('0.003')]
                    for layer in range(1,6):
                        self.bot.grid.tick(self.client.q)
                        grid=self.bot.orders.active({'G'})[0]
                        amount=dec(grid['body']['quantity'])
                        half=floor_step(amount/2,self.client.m['stepSize'])
                        self.client.fill(grid['order_id'],half)
                        self.bot.reconcile()
                        self.assertEqual(self.bot.state['managed']['grid_layer'],layer-1)
                        self.assertEqual(tp_pct_for_grid_layer(self.cfg,self.bot.state['managed']['grid_layer']),rates[layer-1])
                        self.bot.tp.tick(self.client.q); self.bot.reconcile()
                        self.bot.tp.tick(self.client.q); self.bot.reconcile()
                        partial_tp=self.bot.orders.active({'T'})[0]
                        self.assertEqual(dec(partial_tp['body']['quantity']),abs(self.client.qty))
                        expected=bounded_price(self.bot.market,self.client.entry*(1+rates[layer-1]*(-1 if short else 1)),
                                               'BUY' if short else 'SELL')
                        self.assertEqual(dec(partial_tp['body']['price']),expected)
                        self.client.fill(grid['order_id'],amount-half)
                        self.bot.reconcile()
                        self.assertEqual(self.bot.state['managed']['grid_layer'],layer)
                        self.bot.tp.tick(self.client.q); self.bot.reconcile()
                        self.bot.tp.tick(self.client.q); self.bot.reconcile()
                        tp=self.bot.orders.active({'T'})[0]
                        expected=bounded_price(self.bot.market,self.client.entry*(1+rates[layer]*(-1 if short else 1)),
                                               'BUY' if short else 'SELL')
                        self.assertEqual(dec(tp['body']['price']),expected)
                        self.assertEqual(dec(tp['body']['quantity']),abs(self.client.qty))
                        self.assertTrue(tp['body']['reduceOnly'])
                        count=self.client.placed
                        self.bot=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
                        self.bot.recover(); self.bot.tp.tick(self.client.q)
                        self.assertEqual(self.bot.state['managed']['grid_layer'],layer)
                        self.assertEqual(self.bot.tp.target(self.bot.position()),expected)
                        self.assertEqual(self.client.placed,count)
                        last=dec(self.bot.state['managed']['last_fill_price'])
                        self.client.q={'bid':last-1,'ask':last+1,'mid':last}

        def test_87_tp_tier_configuration_and_unknown_layer(self):
            for layer in (-1,6,True,1.5,'3',None):
                with self.subTest(layer=layer):
                    with self.assertRaises(SafetyError): tp_pct_for_grid_layer(self.cfg,layer)
            for tiers in (None,[],[0.007]*5,[0]*6,[1]*6,[-0.1]*6):
                with self.subTest(tiers=tiers):
                    cfg=copy.deepcopy(self.cfg); cfg['take_profit_pct_by_grid_layer']=tiers
                    path=Path(self.tmp.name)/'invalid-tp.json'
                    path.write_text(json.dumps(cfg))
                    with self.assertRaises(SafetyError): load_config(path)
            self.bot.state['managed'].update(grid_layer=5,last_fill_price='120000')
            self.cfg['take_profit_pct']=0.5  # Compatibility field must not override the G5 schedule.
            self.assertEqual(self.bot.tp.target({'qty':'1','entry':'86000'}),dec(86258))
            self.assertEqual(self.bot.tp.target({'qty':'-1','entry':'86000'}),dec(85742))

        def test_88_restart_ignores_stale_local_position_after_manual_flat(self):
            self.filled_entry()
            self.bot.tp.tick(self.client.quote()); self.bot.reconcile()
            self.bot.grid.tick(self.client.quote()); self.bot.reconcile()
            for record in self.bot.orders.active():
                self.client.cancel(record)
            self.client.qty=Decimal('0'); self.client.entry=Decimal('0'); self.client.seq+=1
            count=self.client.placed
            restarted=Bot(self.cfg,self.client,Feed(),self.path,emit=lambda *a,**k:None)
            restarted.recover()
            self.assertFalse(restarted.position())
            restarted.tick()
            self.assertEqual(restarted.state['state'],'WAIT')
            self.assertFalse(restarted.state['orders'])
            self.assertEqual(self.client.placed,count)

        def test_89_manual_flat_before_submission_blocks_tp_and_grid(self):
            self.filled_entry()
            self.client.qty=Decimal('0'); self.client.entry=Decimal('0'); self.client.seq+=1
            count=self.client.placed; journal=copy.deepcopy(self.bot.state['orders'])
            for role,side,reduce in [('T','SELL',True),('G','BUY',False),('X','SELL',True)]:
                with self.subTest(role=role):
                    with self.assertRaisesRegex(SafetyError,'真实仓位数量/均价已变化'):
                        self.bot.orders.submit(role,1 if role=='G' else 0,side,dec(1),dec(99),'GTT',reduce)
                    self.assertEqual(self.client.placed,count)
                    self.assertEqual(self.bot.state['orders'],journal)

        def test_90_manual_position_before_entry_blocks_new_entry(self):
            self.client.qty=Decimal('-1'); self.client.entry=Decimal('101'); self.client.seq+=1
            with self.assertRaisesRegex(SafetyError,'真实仓位数量/均价已变化'):
                self.entry()
            self.assertEqual(self.client.placed,0)
            self.assertFalse(self.bot.state['orders'])

        def test_91_changed_real_average_requires_reconciliation_before_tp(self):
            self.filled_entry()
            self.client.entry=Decimal('98'); self.client.seq+=1
            count=self.client.placed
            with self.assertRaisesRegex(SafetyError,'真实仓位数量/均价已变化'):
                self.bot.tp.tick(self.client.quote())
            self.assertEqual(self.client.placed,count)
            self.bot.reconcile()
            self.assertEqual(dec(self.bot.position()['entry']),dec(98))
            self.bot.tp.tick(self.client.quote())
            tp=self.bot.orders.active({'T'})[0]
            self.assertEqual(dec(tp['body']['price']),self.bot.tp.target(self.bot.position()))
            self.assertTrue(tp['body']['reduceOnly'])

        def test_92_account_failure_or_rollback_never_falls_back_to_local_state(self):
            self.filled_entry()
            count=self.client.placed; journal=copy.deepcopy(self.bot.state['orders'])
            with patch.object(self.client,'account',side_effect=SafetyError('模拟账户API失败')):
                with self.assertRaisesRegex(SafetyError,'账户API失败'):
                    self.bot.tp.tick(self.client.quote())
            stale=self.client.account(); stale['sequence']=0
            with patch.object(self.client,'account',return_value=stale):
                with self.assertRaisesRegex(SafetyError,'快照回退'):
                    self.bot.tp.tick(self.client.quote())
            self.assertEqual(self.client.placed,count)
            self.assertEqual(self.bot.state['orders'],journal)

        def test_93_current_equity_multipliers_no_extra_leverage(self):
            self.assertEqual(base_cfg['first_order_size'],1.5)
            self.assertEqual(base_cfg['grid_order_sizes'],[1.5,3.0,3.0,4.0,5.0])
            self.assertEqual(base_cfg['grid_spacings'],[0.005,0.007,0.009,0.012,0.015])
            cfg=copy.deepcopy(base_cfg)
            # Isolate sizing from production caps, which remain unchanged.
            cfg.update(max_symbol_equity_pct=30,max_account_equity_pct=30,max_margin_equity_pct=0.9)
            account={'equity':'1000','free':'1000','positions':{}}
            q={'bid':dec(100),'ask':dec(100),'mid':dec(100)}
            held=dec(0); amounts=[]
            for multiple in [cfg['first_order_size'],*cfg['grid_order_sizes']]:
                qty=opening_quantity(cfg,account,{'qty':str(held)},self.client.m,q,100,multiple)
                amounts.append(qty*100); held+=qty
            self.assertEqual(amounts,list(map(dec,[1500,1500,3000,3000,4000,5000])))
            self.assertEqual(sum(amounts),dec(18000))
            account['equity']='1200'
            qty=opening_quantity(cfg,account,{},self.client.m,q,100,cfg['first_order_size'])
            self.assertEqual(qty*100,dec(1800))

        def test_94_new_sizes_preserve_production_risk_caps(self):
            cfg=copy.deepcopy(base_cfg)
            account={'equity':'1000','free':'1000','positions':{}}
            q={'bid':dec(100),'ask':dec(100),'mid':dec(100)}
            held=dec(0); total=dec(0)
            for multiple in [cfg['first_order_size'],*cfg['grid_order_sizes']]:
                qty=opening_quantity(cfg,account,{'qty':str(held)},self.client.m,q,100,multiple)
                held+=qty; total+=qty*100
            self.assertEqual(total,dec(18000))
            self.assertEqual(qty*100,dec(5000))
            self.assertEqual(dec(cfg['max_symbol_equity_pct']),dec(20))
            self.assertEqual(dec(cfg['max_account_equity_pct']),dec(20))
            self.assertEqual(dec(cfg['max_margin_equity_pct'])*cfg['leverage'],dec(20))
            capped=opening_quantity(cfg,account,{'qty':'180'},self.client.m,q,100,5)
            self.assertEqual(capped*100,dec(2000))
            with self.assertRaisesRegex(SafetyError,'可用仓位预算不足'):
                opening_quantity(cfg,account,{'qty':'200'},self.client.m,q,100,1)

    with patch(__name__+'.requests.post',side_effect=AssertionError('self-test禁止真实Telegram网络请求')):
        result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests))
    return 0 if result.wasSuccessful() else 1



def run_pair_tests(base_cfg):
    """Offline exchange simulation: no credential loading, HTTP, or Telegram delivery."""
    import unittest
    from unittest.mock import patch
    cfg=copy.deepcopy(base_cfg)
    cfg.update(hedge_enabled=True,hedge_symbol='ETH-USD',hedge_leverage=25,grid_enabled=False,rsi_period=12,
               rsi_long_threshold=45,rsi_short_threshold=55,
               first_order_size=5.0,size_unit='equity_fraction',entry_timeout_sec=300,take_profit_pct=0.008,
               entry_limit_offset_pct=0.001,dry_run=False,wallet_address='',api_signing_key='',
               telegram_enabled=False,telegram_bot_token='',telegram_chat_id='')

    class Feed:
        def healthy(self): return True
        def find(self,*args): return None

    class Exchange:
        def __init__(self):
            self.cfg=copy.deepcopy(cfg); self.address='0x'+'1'*40; self.account_index=0
            self.t=1800000000.; self.seq=1; self.rows={}; self.positions={}; self.placed=[]
            self.equity=dec(1000); self.timeout=False; self.hidden=False; self.cancel_pending=False
            self.auto_market=False; self.account_fail=False; self.stale_sequence=False
            self.prices={PAIR[0]:dec(80000),PAIR[1]:dec(4000)}
            self.markets={s:dict(marketId=i+1,marketDisplayName=s,status='ONLINE',tickSize='0.1',
                stepSize='0.000001' if i==0 else '0.001',minOrderSize='0.0001' if i==0 else '0.001',
                minOrderNotional='5',maxOrderSize='1000',initialMarginFraction='0.01') for i,s in enumerate(PAIR)}
        def now(self): return self.t
        def nonce(self): return int(self.t*1e9)
        def sync_time(self): pass
        def account_params(self): return dict(address=self.address,accountIndex=0)
        def market(self,symbol=None): return self.markets[symbol or PAIR[0]]
        def quote(self,symbol=None):
            p=self.prices[symbol or PAIR[0]]
            return dict(bid=p-dec('0.1'),ask=p+dec('0.1'),mid=p)
        def verify_leverage(self,m): pass
        def account(self):
            if self.account_fail: raise SafetyError('模拟账户读取失败')
            return dict(equity=str(self.equity),free=str(self.equity),deposits=str(self.equity),
                        sequence=0 if self.stale_sequence else self.seq,positions=copy.deepcopy(self.positions))
        def open_orders(self,symbol=None):
            return [] if self.hidden else [copy.deepcopy(r) for r in self.rows.values()
                   if not order_terminal(r) and (symbol is None or r['marketDisplayName']==symbol)]
        def order_history(self,start=None,symbol=None):
            return [] if self.hidden else [copy.deepcopy(r) for r in self.rows.values()
                    if symbol is None or r['marketDisplayName']==symbol]
        def order(self,oid): return None if self.hidden else copy.deepcopy(self.rows.get(oid))
        def candles(self,tf):
            assert tf in ('5m','15m')
            step=300 if tf=='5m' else 900; end=int(self.t)//step*step
            return [dict(openTime=(end-step*(30-i))*1000000,isFinal=True,
                         open=100,high=101,low=99,close=100) for i in range(30)]
        def place(self,body,market):
            oid='o'+str(len(self.rows)+1); self.placed.append(copy.deepcopy(body)); self.seq+=1
            r=dict(orderId=oid,clientId=body['clientId'],marketId=market['marketId'],
                   marketDisplayName=market['marketDisplayName'],side=body['orderSide'],status='OPEN',state='OPEN',
                   originalSize=body['quantity'],remainingSize=body['quantity'],filledSize='0',price=body['price'],
                   avgFillPrice='0',timeInForce=body['timeInForce'],orderType=body['orderType'],
                   reduceOnly=body['reduceOnly'],createdAt=int(self.t*1e6),updatedAt=int(self.t*1e6),sequenceNumber=self.seq)
            self.rows[oid]=r
            if self.auto_market and body['orderType']=='MARKET': self.fill(oid,body['quantity'])
            if self.timeout: raise UnknownOutcome('模拟丢失ACK')
            return dict(orderId=oid,clientId=body['clientId'])
        def cancel(self,rec):
            if self.cancel_pending: raise UnknownOutcome('模拟撤单未确认')
            r=next((r for r in self.rows.values() if r['clientId']==rec['body']['clientId']),None)
            if r and not order_terminal(r):
                self.seq+=1;r.update(status='CANCELED',state='CANCELED',sequenceNumber=self.seq,updatedAt=int(self.t*1e6))
        def fill(self,oid,qty,price=None,terminal=False):
            r=self.rows[oid]; symbol=r['marketDisplayName']; n=dec(qty); px=dec(price or self.prices[symbol])
            assert 0<n<=dec(r['remainingSize'])
            pos=self.positions.get(symbol,{}); oldqty=dec(pos.get('qty',0)); signed=n*(1 if r['side']=='BUY' else -1)
            if r['reduceOnly']: assert oldqty*signed<0 and n<=abs(oldqty)
            newqty=oldqty+signed
            avg=(abs(oldqty)*dec(pos.get('entry',0))+n*px)/(abs(oldqty)+n) if not r['reduceOnly'] else dec(pos['entry'])
            if newqty:self.positions[symbol]=dict(qty=str(newqty),entry=str(avg),mark=str(px),notional=str(abs(newqty)*px))
            else:self.positions.pop(symbol,None)
            oldfill=dec(r['filledSize']); total=oldfill+n
            self.seq+=1
            r.update(filledSize=str(total),remainingSize=str(dec(r['originalSize'])-total),
                     avgFillPrice=str((oldfill*dec(r['avgFillPrice'])+n*px)/total),
                     status='FILLED' if total==dec(r['originalSize']) else 'CANCELED' if terminal else 'OPEN',
                     state='FILLED' if total==dec(r['originalSize']) else 'CANCELED' if terminal else 'OPEN',
                     sequenceNumber=self.seq,updatedAt=int(self.t*1e6))

    class Tests(unittest.TestCase):
        def setUp(self):
            self.tmp=tempfile.TemporaryDirectory(); self.path=Path(self.tmp.name)/'state.json'
            self.ex=Exchange(); self.bot=HedgeBot(self.ex.cfg,self.ex,Feed(),self.path,emit=lambda *a,**k:None)
            self.bot.recover(); self.messages=[]
            self.bot.notifications._enqueue=self.messages.append
        def tearDown(self): self.tmp.cleanup()
        def tick(self):
            with patch('builtins.print'): self.bot.tick()
        def entry(self,short=False):
            with patch(__name__+'.calc_rsi',side_effect=[55.1] if short else [44.9]): self.tick()
            return self.bot.active(PAIR[0],{'E'})[0]
        def seed(self,short=False,qty='0.0625'):
            self.bot.state['cycle']='6b49d200abcdef'; self.bot.save()
            rec=self.bot.submit(PAIR[0],'E','SELL' if short else 'BUY',dec(qty),dec(80000),'ALO')
            return rec
        def fill_btc(self,short=False,qty='0.0625'):
            rec=self.seed(short,qty); self.ex.fill(rec['order_id'],qty,80000); self.bot.reconcile(); return rec
        def legs(self,short=False):
            self.fill_btc(short); self.ex.auto_market=True; self.tick(); self.tick()
        def restart(self,path=None):
            b=HedgeBot(self.ex.cfg,self.ex,Feed(),path or self.path,emit=lambda *a,**k:None)
            b.recover(); self.bot=b; self.bot.notifications._enqueue=self.messages.append
        def test_01_g0_equity_five_no_extra_leverage(self):
            rec=self.entry(); self.assertEqual(self.bot.state['pair']['target_btc_notional'],'5000.0')
            actual=dec(rec['body']['quantity'])*dec(rec['body']['price'])
            self.assertLessEqual(actual,5000); self.assertLess(5000-actual,dec('0.0001')*dec(rec['body']['price']))
            self.assertEqual(rec['body']['timeInForce'],'ALO'); self.assertEqual(dec(rec['body']['price']),dec('79920'))
        def test_02_long_btc_short_eth(self):
            self.fill_btc(); self.bot.hedge_tick(); r=self.bot.active(PAIR[1],{'H'})[0]
            self.assertEqual(r['body']['orderSide'],'SELL'); self.assertEqual(r['body']['orderType'],'MARKET')
            self.assertEqual(dec(r['body']['quantity']),dec('1.25')); self.assertEqual(r['body']['timeInForce'],'IOC')
        def test_03_short_btc_long_eth(self):
            self.fill_btc(True); self.bot.hedge_tick(); r=self.bot.active(PAIR[1],{'H'})[0]
            self.assertEqual(r['body']['orderSide'],'BUY'); self.assertEqual(r['body']['orderType'],'MARKET')
            self.assertLess(abs(dec(r['body']['quantity'])*4000-5000),dec(4.1))
        def test_04_equal_dollars_not_equal_coin_qty(self):
            self.legs(); self.assertEqual(abs(self.bot.qty(PAIR[0])),dec('0.0625'))
            self.assertEqual(abs(self.bot.qty(PAIR[1])),dec('1.25'))
            self.assertEqual(self.bot.notionals(),(dec(5000),dec(5000)))
        def test_05_incremental_partial_btc_and_repeated_ticks(self):
            r=self.seed(); self.ex.auto_market=True
            self.ex.fill(r['order_id'],'0.025',80000); self.tick()
            self.assertEqual(self.bot.notionals(),(dec(2000),dec(2000)))
            self.ex.fill(r['order_id'],'0.01875',80000); self.tick()
            self.assertEqual(self.bot.notionals(),(dec(3500),dec(3500)))
            hs=[r for r in self.ex.placed if r['orderType']=='MARKET' and not r['reduceOnly']]
            self.assertEqual([dec(r['quantity']) for r in hs],[dec('0.5'),dec('0.375')])
            for _ in range(4): self.tick()
            self.assertEqual(len([r for r in self.ex.placed if r['orderType']=='MARKET' and not r['reduceOnly']]),2)
        def test_06_tp_real_averages_both_directions(self):
            for short in (False,True):
                with self.subTest(short=short):
                    self.ex.positions={PAIR[0]:dict(qty='-0.1' if short else '0.1',entry='80000'),
                                       PAIR[1]:dict(qty='1' if short else '-1',entry='4000')}
                    self.bot.account=self.ex.account()
                    self.assertEqual(self.bot.tp_target(PAIR[0]),dec(79360 if short else 80640))
                    self.assertEqual(self.bot.tp_target(PAIR[1]),dec(4032 if short else 3968))
        def close_on_tp(self,symbol,partial=False):
            self.legs(); tp=self.bot.active(symbol,{'T'})[0]
            qty=dec(tp['body']['quantity'])/(2 if partial else 1)
            self.ex.fill(tp['order_id'],qty,tp['body']['price']); self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.ex.positions); self.assertFalse(self.ex.open_orders())
            closes=[r for r in self.ex.placed if r['orderType']=='MARKET' and r['reduceOnly']]
            self.assertTrue(closes)
            for r in closes:self.assertTrue(r['reduceOnly'])
        def test_07_btc_tp_flattens_all(self): self.close_on_tp(PAIR[0])
        def test_08_eth_tp_flattens_all(self): self.close_on_tp(PAIR[1])
        def test_09_no_grid_at_any_old_layer(self):
            self.legs()
            for rate in ('0.995','0.988','0.979','0.967','0.952','1.05'):
                self.ex.prices[PAIR[0]]=dec(80000)*dec(rate)
                self.bot.grid.tick(self.ex.quote()); self.tick()
            self.assertFalse(any('_G' in r['clientId'] for r in self.ex.placed))
            with self.assertRaises(SafetyError):self.bot.submit(PAIR[0],'G','BUY',1,80000)
        def test_10_restart_existing_legs_no_duplicate(self):
            self.legs(); count=len(self.ex.placed); self.restart(); self.tick()
            self.assertEqual(len(self.ex.placed),count)
            self.assertEqual(len(self.bot.active(roles={'T'})),2)
        def test_11_repeated_flatten_no_duplicate_closes(self):
            self.legs(); self.ex.auto_market=False
            self.bot.begin_exit('测试'); self.tick()
            closes=self.bot.active(roles={'X'}); self.assertEqual(len(closes),2)
            count=len(self.ex.placed)
            for _ in range(5): self.tick()
            self.assertEqual(len(self.ex.placed),count)
            for r in closes: self.ex.fill(r['order_id'],r['body']['quantity'])
            self.tick(); self.assertEqual(self.bot.state['state'],'WAIT')
        def test_12_restart_before_eth_and_after_lost_ack(self):
            self.fill_btc(); self.restart(); self.ex.timeout=True; self.bot.hedge_tick()
            self.assertEqual(len(self.ex.placed),2)
            self.restart(); self.bot.hedge_tick(); self.assertEqual(len(self.ex.placed),2)
            r=self.bot.active(PAIR[1],{'H'})[0]; self.ex.fill(r['order_id'],r['body']['quantity'])
            self.restart(); self.bot.hedge_tick(); self.assertEqual(len(self.ex.placed),2)
        def test_13_unknown_intent_blocks_resubmission(self):
            self.fill_btc(); self.ex.timeout=True; self.bot.hedge_tick(); self.ex.hidden=True
            for _ in range(3):
                with self.assertRaises(SafetyError):self.tick()
            self.assertEqual(len(self.ex.placed),2)
        def test_14_partial_tp_also_flattens_both(self): self.close_on_tp(PAIR[0],True)
        def test_15_cancel_barrier_before_market_flatten(self):
            # New paired-exit contract: use a live hedge order as the
            # cancellation barrier; do not depend on a single-leg T order.
            self.legs()
            self.bot.submit(
                PAIR[1], 'H', 'SELL', dec('0.1'), dec('4000'), 'GTT'
            )
            self.ex.cancel_pending=True
            count=len(self.ex.placed)

            self.bot.begin_exit('测试')
            self.bot.flatten_all()

            # Cancellation is not confirmed, so no X market close may be sent.
            self.assertEqual(count, len(self.ex.placed))
            self.assertEqual(self.bot.state['state'], 'EXITING')
            self.assertFalse(
                any(r['orderType']=='MARKET' and r['reduceOnly']
                    for r in self.ex.placed[count:])
            )

            # Once cancellation is confirmed, flattening may proceed.
            self.ex.cancel_pending=False
            self.ex.t += self.ex.cfg['cancel_retry_sec'] + 1
            self.bot.flatten_all()

            self.assertEqual(self.bot.state['state'], 'WAIT')
            self.assertFalse(self.ex.positions)
            self.assertFalse(self.ex.open_orders())
        def test_16_entry_timeout_five_minutes_partial_hedge_preserved(self):
            r=self.seed(); self.ex.fill(r['order_id'],'0.025'); self.ex.auto_market=True; self.tick()
            self.ex.t+=299; self.tick(); self.assertFalse(self.bot.state['orders'][r['body']['clientId']]['cancel_requested'])
            self.ex.t+=1; self.tick(); self.assertTrue(self.bot.state['orders'][r['body']['clientId']]['cancel_requested'])
            self.assertEqual(self.bot.notionals(),(dec(2000),dec(2000)))
            self.assertFalse(self.bot.state['exiting'])
        def test_17_d1_state_not_cross_strict_boundaries(self):
            for value,side in [(44.9,'LONG'),(45.0,''),(50.0,''),(55.0,''),(55.1,'SHORT')]:
                with self.subTest(rsi=value),patch(__name__+'.calc_rsi',return_value=value) as calc:
                    r=evaluate_hedge(self.ex.candles('5m'),cfg,now=self.ex.now(),account_known=True)
                    self.assertEqual(r['side'],side)
                    calc.assert_called_once()  # No prior-RSI comparison or second timeframe.
                    self.assertEqual(calc.call_args.args[1],12)
                    self.assertEqual(format_log('BTC-USD',r,cfg),
                        f"BTC 5M RSI12={value:.2f} | LONG条件={str(value<45).upper()} | SHORT条件={str(value>55).upper()} | 开仓方向={side or 'NONE'}")
            ledger={}
            for expected in (True,False):
                with patch(__name__+'.calc_rsi',return_value=44.9):
                    self.assertEqual(evaluate_hedge(self.ex.candles('5m'),cfg,
                        ledger=ledger,now=self.ex.now(),account_known=True)['signal'],expected)
                ledger=json.loads(json.dumps(ledger))  # Persisted dedup survives reload.
        def test_18_only_latest_confirmed_closed_5m(self):
            rows=self.ex.candles('5m')
            invalid=[rows[:-1],rows+[rows[-1]],[],rows[:-1]+[dict(rows[-1],isFinal=False)]]
            for data in invalid:
                with patch(__name__+'.calc_rsi',side_effect=AssertionError('invalid bars must not calculate RSI')):
                    self.assertFalse(evaluate_hedge(data,cfg,now=self.ex.now(),account_known=True)['signal'])
        def test_19_eth_below_minimum_accumulates_residue(self):
            self.ex.markets[PAIR[1]]['minOrderNotional']='100'
            r=self.seed(); self.ex.fill(r['order_id'],'0.001'); self.bot.reconcile(); self.bot.hedge_tick()
            self.assertEqual(len(self.ex.placed),1)
            self.ex.fill(r['order_id'],'0.001'); self.bot.reconcile(); self.bot.hedge_tick()
            self.assertEqual(len(self.ex.placed),2)
            self.assertEqual(self.bot.notionals()[1],0)  # ACK is not a confirmed hedge.
        def test_20_partial_eth_ioc_only_retries_remainder(self):
            self.fill_btc(); self.bot.hedge_tick(); h=self.bot.active(PAIR[1],{'H'})[0]
            self.ex.fill(h['order_id'],'0.5',terminal=True); self.bot.reconcile(); self.bot.hedge_tick()
            h=self.bot.active(PAIR[1],{'H'})[0];self.assertEqual(dec(h['body']['quantity']),dec('0.75'))
        def test_21_restart_without_journal_adopts_existing_dollars(self):
            self.legs(); count=len(self.ex.placed); self.restart(Path(self.tmp.name)/'missing.json'); self.tick()
            self.assertEqual(count,len(self.ex.placed));self.assertEqual(self.bot.notionals(),(dec(5000),dec(5000)))
        def test_22_restart_btc_before_hedge_no_journal(self):
            self.fill_btc();self.restart(Path(self.tmp.name)/'missing.json'); self.bot.hedge_tick()
            self.assertEqual(len(self.ex.placed),2)
        def test_23_external_flat_ends_both(self):
            self.legs();self.ex.positions.pop(PAIR[0]);self.ex.seq+=1
            self.tick();self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.positions)
        def test_24_account_failure_and_sequence_rollback_block_orders(self):
            self.fill_btc();self.ex.account_fail=True
            with self.assertRaises(SafetyError): self.tick()
            self.assertEqual(len(self.ex.placed),1)
            self.ex.account_fail=False;self.ex.stale_sequence=True
            with self.assertRaises(SafetyError): self.tick()
            self.assertEqual(len(self.ex.placed),1)
        def test_25_telegram_events_are_not_repeated(self):
            self.legs(); count=len(self.messages)
            for _ in range(4):self.tick()
            self.assertEqual(len(self.messages),count)
            self.assertEqual(sum('BTC首仓真实成交' in x for x in self.messages),1)
            self.assertEqual(sum('ETH反向仓建立成功' in x for x in self.messages),1)
        def test_26_pending_entry_fill_during_cancel_also_closed(self):
            e=self.seed();self.ex.auto_market=True;self.ex.fill(e['order_id'],'0.025');self.tick()
            tp=self.bot.active(PAIR[1],{'T'})[0];self.ex.fill(tp['order_id'],tp['body']['quantity'])
            original=self.ex.cancel
            def racing(rec):
                if rec['role']=='E' and not order_terminal(self.ex.rows[rec['order_id']]):
                    self.ex.fill(rec['order_id'],self.ex.rows[rec['order_id']]['remainingSize'])
                original(rec)
            with patch.object(self.ex,'cancel',side_effect=racing):self.tick()
            self.assertFalse(self.ex.positions);self.assertEqual(self.bot.state['state'],'WAIT')
        def test_27_risk_limits_preserved(self):
            self.ex.cfg['max_account_equity_pct']=9
            with self.assertRaises(SafetyError):self.entry()
            self.assertFalse(self.ex.placed)
        def test_28_market_body_signing_precision(self):
            self.fill_btc();self.bot.hedge_tick(); r=self.bot.active(PAIR[1],{'H'})[0]
            payload=order_payload(r['body'],self.ex.market(PAIR[1]))
            self.assertEqual(payload['m'],2);self.assertEqual(payload['t'],2);self.assertEqual(payload['q'],1250)
            self.assertGreater(dec(r['body']['price']),0)
        def test_29_old_grid_journal_migration_disables_grid(self):
            self.fill_btc();self.bot.state.pop('pair');self.bot.save();self.restart()
            self.ex.auto_market=True;self.tick()
            self.assertFalse(any('_G' in r['clientId'] for r in self.ex.placed))
            self.assertEqual(self.bot.notionals(),(dec(5000),dec(5000)))

        def test_30_tp_exit_gate_survives_account_failure_and_restart(self):
            self.legs();tp=self.bot.active(PAIR[0],{'T'})[0]
            self.ex.fill(tp['order_id'],tp['body']['quantity']);self.ex.account_fail=True
            with self.assertRaises(SafetyError):self.tick()
            saved=json.loads(self.path.read_text());self.assertTrue(saved['exiting'])
            count=len(self.ex.placed);self.assertEqual(count,len(self.ex.placed))
            self.ex.account_fail=False;self.restart();self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.positions)
        def test_31_partial_market_close_retry_uses_real_remaining(self):
            self.legs();self.ex.auto_market=False;self.bot.begin_exit('测试');self.tick()
            x=self.bot.active(PAIR[0],{'X'})[0]
            self.ex.fill(x['order_id'],'0.025',terminal=True);self.tick()
            remaining=self.bot.active(PAIR[0],{'X'})[0]
            self.assertEqual(dec(remaining['body']['quantity']),dec('0.0375'))
            count=len(self.ex.placed);self.tick();self.assertEqual(len(self.ex.placed),count)
        def test_32_existing_eth_partial_restart_only_missing_dollars(self):
            self.fill_btc();self.bot.hedge_tick();h=self.bot.active(PAIR[1],{'H'})[0]
            self.ex.fill(h['order_id'],'0.5',terminal=True);self.restart();self.bot.hedge_tick()
            h=self.bot.active(PAIR[1],{'H'})[0]
            self.assertEqual(dec(h['body']['quantity']),dec('0.75'))
        def test_33_pending_order_account_ahead_does_not_rehedge(self):
            e=self.seed();oldrow=copy.deepcopy(self.ex.rows[e['order_id']])
            self.ex.fill(e['order_id'],'0.025')
            with patch.object(self.ex,'order',return_value=oldrow),patch.object(self.ex,'open_orders',side_effect=lambda symbol:[oldrow] if symbol==PAIR[0] else []):
                with self.assertRaises(SafetyError):self.tick()
            self.assertFalse(self.bot.state['exiting']);self.assertEqual(len(self.ex.placed),1)
            self.ex.auto_market=True;self.tick();self.assertEqual(self.bot.notionals(),(dec(2000),dec(2000)))
        def test_34_notional_delta_uses_fill_prices_not_quote(self):
            e=self.seed();self.ex.auto_market=True
            self.ex.fill(e['order_id'],'0.025',80000);self.tick()
            self.ex.fill(e['order_id'],'0.0125',80400);self.tick()
            btc,eth=self.bot.notionals()
            self.assertEqual(btc,dec(3005));self.assertLess(abs(btc-eth),dec(5))
        def test_35_tp_reprices_after_real_average_changes(self):
            e=self.seed();self.ex.auto_market=True
            self.ex.fill(e['order_id'],'0.025',80000);self.tick()
            old=self.bot.active(PAIR[0],{'T'})[0]
            self.ex.fill(e['order_id'],'0.0125',80400);self.tick();self.tick()
            new=self.bot.active(PAIR[0],{'T'})[0]
            self.assertNotEqual(old['body']['price'],new['body']['price'])
            self.assertEqual(dec(new['body']['price']),self.bot.tp_target(PAIR[0]))
            self.assertEqual(dec(new['body']['quantity']),abs(self.bot.qty(PAIR[0])))
        def test_36_tp_chunks_cover_all_real_position(self):
            self.legs();self.bot.begin_exit('测试');self.tick()
            self.ex=Exchange();self.ex.auto_market=True
            self.bot=HedgeBot(self.ex.cfg,self.ex,Feed(),Path(self.tmp.name)/'chunks.json',emit=lambda *a,**k:None)
            self.bot.recover();self.fill_btc();self.bot.hedge_tick();self.bot.reconcile()
            self.ex.markets[PAIR[0]]['maxOrderSize']='0.02'
            self.bot.tp_tick(PAIR[0]);ts=self.bot.active(PAIR[0],{'T'})
            self.assertEqual(len(ts),4)
            self.assertEqual(sum(dec(r['body']['quantity']) for r in ts),dec('0.0625'))
            count=len(self.ex.placed);self.bot.tp_tick(PAIR[0]);self.assertEqual(count,len(self.ex.placed))
        def test_37_foreign_eth_order_blocks_new_cycle(self):
            body=make_body(self.ex,self.ex.market(PAIR[1]),'BUY',dec(1),dec(3990),'ALO',False,'foreign')
            self.ex.place(body,self.ex.market(PAIR[1]))
            with self.assertRaises(SafetyError):self.entry()
            self.assertEqual(len(self.ex.placed),1)
        def test_38_eth_only_recovery_flattens_no_new_btc(self):
            self.ex.positions[PAIR[1]]=dict(qty='1',entry='4000',notional='4000',mark='4000')
            self.ex.seq+=1;self.ex.auto_market=True
            self.restart(Path(self.tmp.name)/'eth-only.json');self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))
        def test_39_flatten_waits_for_both_positions_and_orders(self):
            self.legs();self.ex.auto_market=False;self.bot.begin_exit('测试');self.tick()
            x=self.bot.active(PAIR[0],{'X'})[0];self.ex.fill(x['order_id'],x['body']['quantity']);self.tick()
            self.assertEqual(self.bot.state['state'],'EXITING');self.assertTrue(self.bot.qty(PAIR[1]))
            x=self.bot.active(PAIR[1],{'X'})[0];self.ex.fill(x['order_id'],x['body']['quantity']);self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.open_orders())
        def test_40_dry_run_observes_both_markets_without_orders(self):
            dry=copy.deepcopy(cfg);dry['dry_run']=True
            with patch(__name__+'.calc_rsi',return_value=44.9),patch('builtins.print'):
                r=observe_pair_once(self.ex,dry,Path(self.tmp.name)/'dry.json')
            self.assertTrue(r['signal']);self.assertFalse(self.ex.placed)
        def test_41_nonfinal_live_candle_never_enters_rsi(self):
            five=self.ex.candles('5m')
            for final in (False,True):
                rows=five+[dict(five[-1],openTime=int(self.ex.now()*1e6),isFinal=final,close=999999)]
                with patch(__name__+'.calc_rsi',return_value=44.9) as calc:
                    r=evaluate_hedge(rows,cfg,now=self.ex.now(),account_known=True)
                self.assertTrue(r['signal'])
                calc.assert_called_once_with([x['close'] for x in five],12)
                self.assertEqual(r['bar_5m'],int(self.ex.now())//300*300-300)
        def test_42_hedge_and_tp_changes_validated(self):
            for key,value in [('grid_enabled',True),('first_order_size',1.5),('rsi_period',7),('take_profit_pct',0.007),('entry_timeout_sec',90)]:
                bad=copy.deepcopy(cfg);bad[key]=value
                with self.assertRaises(ValueError):validate_config(bad)
        def test_43_tp_during_hedge_submission_blocks_new_exposure(self):
            self.legs();self.ex.auto_market=False
            tp=self.bot.active(PAIR[0],{'T'})[0];self.ex.fill(tp['order_id'],tp['body']['quantity'])
            count=len(self.ex.placed)
            with self.assertRaises(SafetyError):self.bot.submit(PAIR[1],'H','SELL',dec(1),dec(3995),'IOC',False,True)
            self.assertTrue(self.bot.state['exiting']);self.assertEqual(len(self.ex.placed),count)
        def test_44_zero_fill_entry_cancel_finishes_cycle(self):
            self.entry();self.ex.t+=300;self.tick();self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.positions)
            self.assertEqual(len(self.ex.placed),1)
        def test_45_daily_halt_does_not_open_new_cycle(self):
            self.bot.risk.update_daily();self.bot.state['daily']['halted']=True;self.bot.save()
            with patch(__name__+'.calc_rsi',side_effect=AssertionError('halt must skip signal')):self.tick()
            self.assertFalse(self.ex.placed)


        def test_46_each_market_verifies_own_leverage(self):
            client=ArcusClient(cfg)
            for symbol,value,fraction in [(PAIR[0],40,'0.025'),(PAIR[1],25,'0.04')]:
                market=dict(self.ex.market(symbol),initialMarginFraction=fraction)
                with patch.object(client,'account_params',return_value={}), patch.object(client,'request',return_value={
                        'leverages':[dict(marketId=market['marketId'],leverage=value,marginMode='CROSS')]}) as request:
                    client.verify_leverage(market)
                    self.assertEqual(request.call_args.args[2]['market'],symbol)
            market=dict(self.ex.market(PAIR[1]),initialMarginFraction='0.04')
            with patch.object(client,'account_params',return_value={}), patch.object(client,'request',return_value={
                    'leverages':[dict(marketId=2,leverage=40,marginMode='CROSS')]}):
                with self.assertRaises(SafetyError):client.verify_leverage(market)

        def test_47_margin_reserves_both_legs_at_their_leverage(self):
            # 5000/40 + 5000/25 = 325 USD, not 10000/40 = 250 USD.
            self.ex.cfg['max_margin_equity_pct']=0.30
            with self.assertRaises(SafetyError):self.entry()
            self.assertFalse(self.ex.placed)

        def test_48_live_and_observer_fetch_only_5m(self):
            original=self.ex.candles
            def candles(tf):
                self.assertEqual(tf,'5m')
                return original(tf)
            with patch.object(self.ex,'candles',side_effect=candles) as fetch:
                self.entry()
                self.assertEqual([x.args[0] for x in fetch.call_args_list],['5m'])
            with patch.object(self.ex,'candles',side_effect=candles) as fetch,patch(__name__+'.calc_rsi',return_value=44.9),patch('builtins.print'):
                observe_pair_once(self.ex,cfg,Path(self.tmp.name)/'observer.json')
                self.assertEqual([x.args[0] for x in fetch.call_args_list],['5m'])
        def test_49_pending_positions_and_exiting_never_reenter_d1(self):
            e=self.seed()
            with patch(__name__+'.evaluate_hedge',side_effect=AssertionError('cycle must not enter D1')):
                self.tick()  # BTC entry pending.
                self.ex.auto_market=True;self.ex.fill(e['order_id'],e['body']['quantity'])
                self.tick();self.tick()  # Both legs are being managed.
                self.bot.begin_exit('测试');self.tick()  # EXITING.
            self.assertEqual(sum('_E0_' in r['clientId'] for r in self.ex.placed),1)
            for kw in ({'account_known':False},{'position_side':'LONG'},{'has_entry_order':True}):
                args={'account_known':True,**kw}
                with patch(__name__+'.calc_rsi',return_value=44.9):
                    self.assertFalse(evaluate_hedge(self.ex.candles('5m'),cfg,now=self.ex.now(),**args)['signal'])
        def test_50_d1_boundaries_reach_at_most_one_entry(self):
            for index,(value,side) in enumerate([(44.9,'BUY'),(45.0,''),(50.0,''),(55.0,''),(55.1,'SELL')]):
                self.ex=Exchange()
                self.bot=HedgeBot(self.ex.cfg,self.ex,Feed(),Path(self.tmp.name)/f'd1-{index}.json',emit=lambda *a,**k:None)
                self.bot.recover()
                with patch(__name__+'.calc_rsi',return_value=value):
                    for _ in range(3):self.tick()
                self.assertEqual(len(self.ex.placed),1 if side else 0)
                if side:
                    self.assertEqual(self.ex.placed[0]['orderSide'],side)
                    self.restart(self.bot.path)
                    with patch(__name__+'.calc_rsi',return_value=value):self.tick()
                    self.assertEqual(len(self.ex.placed),1)

        def test_51_daily_halt_logs_every_scan_without_clearing(self):
            self.bot.risk.update_daily()
            self.bot.state['daily']['halted']=True
            self.bot.save()
            before=copy.deepcopy(self.bot.state['daily'])
            with patch('builtins.print') as output, patch(__name__+'.evaluate_hedge',side_effect=AssertionError('halted must not enter D1')):
                for _ in range(3):self.bot.tick()
            lines=[call.args[0] for call in output.call_args_list]
            self.assertEqual(sum('[WAIT] reason=DAILY_HALTED' in line for line in lines),3)
            self.assertTrue(all('BTC订单=0 | ETH订单=0 | BTC仓位=0 | ETH仓位=0' in line for line in lines))
            self.assertEqual(self.bot.state['daily'],before)
            self.assertTrue(json.loads(self.path.read_text())['daily']['halted'])
            self.assertFalse(self.ex.placed)

        def test_52_cooldown_logs_remaining_then_allows_d1(self):
            self.bot.state['cooldown_until']=self.ex.now()+45
            self.bot.save()
            with patch('builtins.print') as output, patch(__name__+'.evaluate_hedge',side_effect=AssertionError('cooldown must not enter D1')):
                self.bot.tick()
                self.ex.t+=22
                self.bot.tick()
            self.assertIn('remaining=45.0秒',output.call_args_list[0].args[0])
            self.assertIn('remaining=23.0秒',output.call_args_list[1].args[0])
            self.assertTrue(all('[WAIT] reason=COOLDOWN' in c.args[0] for c in output.call_args_list))
            self.ex.t+=23
            with patch('builtins.print') as output,patch(__name__+'.calc_rsi',return_value=50) as calc:
                self.bot.tick()
            calc.assert_called_once()
            self.assertIn('BTC 5M RSI12=50.00',output.call_args.args[0])
            self.assertFalse(self.ex.placed)

        def test_53_wait_order_and_position_guards_have_diagnostics(self):
            # Isolate these defensive guards; production reconciliation can reject inconsistent
            # WAIT snapshots earlier, and must not be weakened to make them reachable.
            for kind in ('ACTIVE_ORDER','POSITION_EXISTS'):
                self.ex.positions={}
                self.bot.state['cycle']=None
                self.bot.state['orders']={}
                self.bot.state['state']='WAIT'
                if kind=='ACTIVE_ORDER':
                    self.bot.state['orders']={str(i):dict(symbol=s,terminal=False) for i,s in enumerate(PAIR)}
                else:
                    self.ex.positions={PAIR[0]:dict(qty='0.01',entry='80000',notional='800'),
                                       PAIR[1]:dict(qty='-0.2',entry='4000',notional='800')}
                self.bot.account=self.ex.account()
                with patch.object(self.bot,'reconcile'),patch('builtins.print') as output, \
                     patch(__name__+'.evaluate_hedge',side_effect=AssertionError('guard must block D1')):
                    self.bot.tick()
                line=output.call_args.args[0]
                self.assertIn('[WAIT] reason='+kind,line)
                if kind=='ACTIVE_ORDER':self.assertIn('BTC订单=1 | ETH订单=1',line)
                else:self.assertIn('BTC仓位=0.01 | ETH仓位=-0.2',line)
                self.assertFalse(self.ex.placed)

        def test_54_cycle_and_exit_waits_are_visible(self):
            e=self.seed()
            with patch('builtins.print') as output,patch(__name__+'.evaluate_hedge',side_effect=AssertionError('cycle must not enter D1')):
                self.bot.tick()
            self.assertIn('[WAIT] reason=CYCLE_ACTIVE',output.call_args.args[0])
            self.assertIn('BTC订单=1',output.call_args.args[0])
            self.bot.begin_exit('诊断测试')
            with patch('builtins.print') as output:
                self.bot.tick()
            self.assertTrue(any('[WAIT] reason=EXITING' in c.args[0] for c in output.call_args_list))
            self.assertFalse(self.ex.open_orders())
            self.assertEqual(self.bot.state['state'],'WAIT')

        def test_55_unblocked_wait_prints_d1_on_every_scan(self):
            with patch('builtins.print') as output,patch(__name__+'.calc_rsi',return_value=50) as calc:
                for _ in range(3):
                    self.bot.tick()
                    self.ex.t+=self.ex.cfg['scan_interval_sec']
            self.assertEqual(calc.call_count,3)
            expected='BTC 5M RSI12=50.00 | LONG条件=FALSE | SHORT条件=FALSE | 开仓方向=NONE'
            self.assertEqual([c.args[0] for c in output.call_args_list],[expected]*3)
            self.assertFalse(self.ex.placed)

        def test_56_telegram_failure_does_not_prevent_d1(self):
            with patch.object(self.bot.notifications,'_enqueue',side_effect=OSError('offline')),patch('builtins.print'):
                self.bot.notifications.safe('startup')
            with patch('builtins.print') as output,patch(__name__+'.calc_rsi',return_value=50) as calc:
                self.bot.tick()
            calc.assert_called_once()
            self.assertIn('BTC 5M RSI12=50.00',output.call_args.args[0])
            self.assertFalse(self.ex.placed)

        def test_57_wait_logging_failure_never_bypasses_guard(self):
            self.bot.risk.update_daily()
            self.bot.state['daily']['halted']=True
            with patch('builtins.print',side_effect=BrokenPipeError()), \
                 patch(__name__+'.evaluate_hedge',side_effect=AssertionError('halt must remain active')):
                self.bot.tick()
            self.assertTrue(self.bot.state['daily']['halted'])
            self.assertFalse(self.ex.placed)

        def test_58_restart_preserves_daily_halt_and_reports_it(self):
            self.bot.risk.update_daily()
            self.bot.state['daily']['halted']=True
            self.bot.state['cooldown_until']=self.ex.now()-300
            self.bot.save()
            self.restart()
            with patch('builtins.print') as output,patch(__name__+'.evaluate_hedge',side_effect=AssertionError('restart cannot bypass halt')):
                self.bot.tick()
            self.assertIn('[WAIT] reason=DAILY_HALTED',output.call_args.args[0])
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertIsNone(self.bot.state['cycle'])
            self.assertFalse(self.bot.state['orders'])
            self.assertFalse(self.bot.state['exiting'])
            self.assertTrue(self.bot.state['daily']['halted'])

        def external_pair(self,short=False,btc_qty='0.0625',eth_qty='1.25',btc_entry='80000',eth_entry='4000'):
            self.ex.positions={
                PAIR[0]:dict(qty=str(dec(btc_qty)*(-1 if short else 1)),entry=btc_entry,mark=btc_entry,
                             notional=str(dec(btc_qty)*dec(btc_entry))),
                PAIR[1]:dict(qty=str(dec(eth_qty)*(1 if short else -1)),entry=eth_entry,mark=eth_entry,
                             notional=str(dec(eth_qty)*dec(eth_entry)))}
            self.ex.seq+=1

        def test_59_persisted_wait_restart_adopts_both_real_sides(self):
            for short in (False,True):
                self.ex=Exchange()
                path=Path(self.tmp.name)/f'adopt-{short}.json'
                self.bot=HedgeBot(self.ex.cfg,self.ex,Feed(),path,emit=lambda *a,**k:None)
                self.bot.recover()
                self.external_pair(short)
                self.ex.prices={PAIR[0]:dec(81000),PAIR[1]:dec(4050)}
                self.restart(path)
                self.tick()
                self.assertEqual(self.bot.notionals(),(dec(5000),dec(5000)))
                self.assertEqual(len(self.ex.placed),2)
                self.assertTrue(all(r['reduceOnly'] and '_T' in r['clientId'] for r in self.ex.placed))
                btc_tp=self.bot.active(PAIR[0],{'T'})[0]['body']
                eth_tp=self.bot.active(PAIR[1],{'T'})[0]['body']
                self.assertEqual(dec(btc_tp['quantity']),dec('0.0625'))
                self.assertEqual(dec(eth_tp['quantity']),dec('1.25'))
                self.assertEqual(dec(btc_tp['price']),dec(79360 if short else 80640))
                self.assertEqual(dec(eth_tp['price']),dec(4032 if short else 3968))
                cycle=self.bot.state['cycle'];count=len(self.ex.placed)
                self.restart(path);self.tick()
                self.assertEqual(self.bot.state['cycle'],cycle)
                self.assertEqual(len(self.ex.placed),count)

        def test_60_live_wait_adopts_without_rsi_or_new_btc(self):
            self.external_pair()
            with patch(__name__+'.evaluate_hedge',side_effect=AssertionError('adoption must skip D1')):
                self.tick()
            self.assertIsNotNone(self.bot.state['cycle'])
            self.assertEqual(len(self.bot.active(roles={'T'})),2)
            self.assertFalse(any('_E' in r['clientId'] or '_H' in r['clientId'] for r in self.ex.placed))

        def test_61_btc_only_adoption_hedges_real_entry_value(self):
            self.external_pair(btc_entry='80400')
            self.ex.positions.pop(PAIR[1]);self.ex.auto_market=True
            self.tick();self.tick()
            self.assertEqual(self.bot.notionals()[0],dec(5025))
            self.assertLess(abs(self.bot.notionals()[0]-self.bot.notionals()[1]),5)
            self.assertFalse(any('_E' in r['clientId'] for r in self.ex.placed))
            h=[r for r in self.ex.placed if '_H' in r['clientId']]
            self.assertEqual(len(h),1)
            self.assertEqual(h[0]['orderSide'],'SELL')

        def test_62_existing_partial_eth_only_hedges_deficit(self):
            self.external_pair(eth_qty='0.5');self.ex.auto_market=True
            self.tick();self.tick()
            hs=[r for r in self.ex.placed if '_H' in r['clientId']]
            self.assertEqual(len(hs),1)
            self.assertEqual(dec(hs[0]['quantity']),dec('0.75'))
            self.assertEqual(self.bot.notionals(),(dec(5000),dec(5000)))

        def test_63_adopted_quantity_increase_refreshes_tp_no_duplicate_hedge(self):
            self.external_pair();self.tick()
            self.external_pair(btc_qty='0.075',eth_qty='1.5')
            self.tick();self.tick()
            self.assertEqual(self.bot.notionals(),(dec(6000),dec(6000)))
            self.assertEqual(sum(dec(r['body']['quantity']) for r in self.bot.active(PAIR[0],{'T'})),dec('0.075'))
            self.assertEqual(sum(dec(r['body']['quantity']) for r in self.bot.active(PAIR[1],{'T'})),dec('1.5'))
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))

        def test_64_same_quantity_new_real_average_updates_basis_and_tp(self):
            self.external_pair();self.tick()
            self.external_pair(btc_entry='80800',eth_entry='4040')
            self.tick();self.tick()
            self.assertEqual(self.bot.notionals(),(dec(5050),dec(5050)))
            for symbol in PAIR:
                tp=self.bot.active(symbol,{'T'})[0]
                self.assertEqual(dec(tp['body']['price']),self.bot.tp_target(symbol))
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))

        def test_65_adoption_does_not_override_exiting(self):
            self.external_pair();self.tick()
            self.bot.begin_exit('已有退出指令');self.ex.auto_market=True
            self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.ex.positions)
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))

        def test_66_adoption_preserves_daily_halt_cooldown_and_ledger(self):
            self.bot.risk.update_daily();self.bot.state['daily']['halted']=True
            self.bot.state['cooldown_until']=self.ex.now()+300
            self.bot.state['ledger']={'last_signal_bar':int(self.ex.now())-300,
                                     'last_signal_bar_5m':int(self.ex.now())-300,
                                     'last_signal_side':'LONG','signal_time':self.ex.now()}
            before={k:copy.deepcopy(self.bot.state[k]) for k in ('daily','cooldown_until','ledger')}
            self.external_pair();self.bot.reconcile()
            for key,value in before.items():self.assertEqual(self.bot.state[key],value)
            self.assertFalse(self.ex.placed)

        def test_67_adoption_requires_stable_fresh_account(self):
            self.external_pair();original=self.ex.account;calls=[]
            def account():
                result=original();calls.append(1)
                if len(calls)>=2:
                    result['positions'][PAIR[0]]['entry']='80100'
                return result
            with patch.object(self.ex,'account',side_effect=account):
                with self.assertRaises(SafetyError):self.bot.reconcile()
            self.assertIsNone(self.bot.state['cycle']);self.assertFalse(self.ex.placed)

        def test_68_unknown_order_blocks_adoption(self):
            self.fill_btc();self.ex.timeout=True;self.bot.hedge_tick()
            self.external_pair();self.ex.hidden=True
            with patch.object(self.bot,'adopt_positions',side_effect=AssertionError('unknown intent must block adoption')):
                with self.assertRaises(SafetyError):self.bot.reconcile()
            self.assertEqual(len(self.ex.placed),2)

        def test_69_foreign_order_blocks_adoption(self):
            self.external_pair()
            body=make_body(self.ex,self.ex.market(PAIR[1]),'BUY',dec(1),dec(3990),'ALO',False,'foreign')
            self.ex.place(body,self.ex.market(PAIR[1]))
            with self.assertRaises(SafetyError):self.bot.reconcile()
            self.assertIsNone(self.bot.state['cycle']);self.assertEqual(len(self.ex.placed),1)

        def test_70_adopted_tp_flattens_and_cools_exactly_sixty_seconds(self):
            self.assertEqual(self.ex.cfg['cooldown_seconds'],60)
            self.external_pair();self.ex.auto_market=True;self.tick()
            tp=self.bot.active(PAIR[0],{'T'})[0]
            self.ex.fill(tp['order_id'],tp['body']['quantity']);self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertEqual(self.bot.state['cooldown_until']-self.ex.now(),60)
            self.ex.t+=59
            with patch(__name__+'.evaluate_hedge',side_effect=AssertionError('still cooling')):self.tick()
            self.ex.t+=1
            with patch(__name__+'.calc_rsi',return_value=50) as calc:self.tick()
            calc.assert_called_once()

        def test_71_eth_only_or_same_direction_keeps_abnormal_flatten(self):
            self.external_pair();self.ex.positions.pop(PAIR[0]);self.ex.auto_market=True
            self.tick();self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.positions)
            self.external_pair();self.ex.positions[PAIR[1]]['qty']='1.25'
            self.tick();self.assertEqual(self.bot.state['state'],'WAIT');self.assertFalse(self.ex.positions)
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))


        def test_72_adoption_never_uses_local_price_when_account_fails(self):
            self.external_pair();self.ex.account_fail=True
            with self.assertRaises(SafetyError):self.bot.reconcile()
            self.assertIsNone(self.bot.state['cycle']);self.assertFalse(self.ex.placed)
            self.ex.account_fail=False;self.ex.stale_sequence=True
            with self.assertRaises(SafetyError):self.bot.reconcile()
            self.assertIsNone(self.bot.state['cycle']);self.assertFalse(self.ex.placed)

        def test_73_reversed_external_pair_replaces_wrong_direction_tp(self):
            self.external_pair();self.tick()
            self.external_pair(short=True)
            self.tick();self.tick()
            for symbol,side in [(PAIR[0],'BUY'),(PAIR[1],'SELL')]:
                active=self.bot.active(symbol,{'T'})
                self.assertTrue(active)
                self.assertTrue(all(r['body']['orderSide']==side for r in active))
            self.assertTrue(all(r['reduceOnly'] for r in self.ex.placed))

        def test_74_external_position_notice_only_after_confirmed_flat(self):
            self.legs()
            self.messages.clear()
            self.ex.auto_market=False
            self.ex.positions.pop(PAIR[0]);self.ex.seq+=1
            self.tick()
            self.assertTrue(self.bot.state['exiting'])
            self.assertTrue(self.bot.qty(PAIR[1]))
            self.assertEqual(self.messages,[])  # No premature success/start notification.
            self.tick()
            self.assertEqual(self.messages,[])
            rec=self.bot.active(PAIR[1],{'X'})[0]
            self.ex.fill(rec['order_id'],rec['body']['quantity'])
            self.tick()
            self.assertFalse(self.ex.positions)
            self.assertFalse(self.ex.open_orders())
            expected='外部真实仓位变化，全部仓位归零\nBTC=0，ETH=0，双腿本轮挂单=0\n本轮结束，开始轮巡'
            self.assertEqual(self.messages,[expected])
            self.tick();self.restart();self.tick()
            self.assertEqual(self.messages,[expected])

        def test_75_unfilled_entry_notice_after_confirmed_cancel_only(self):
            self.entry()
            self.messages.clear()
            self.ex.cancel_pending=True
            self.ex.t+=300
            self.tick();self.tick()
            self.assertEqual(self.messages,[])
            self.assertTrue(self.bot.active(PAIR[0],{'E'}))
            self.ex.cancel_pending=False
            self.ex.t+=self.ex.cfg['cancel_retry_sec']+1
            self.tick();self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.ex.positions)
            self.assertFalse(self.ex.open_orders())
            expected='首仓未成交或外部平仓\n全部仓位归零\nBTC=0，ETH=0，双腿本轮挂单=0\n本轮结束，开始下一轮'
            self.assertEqual(self.messages,[expected])
            self.assertEqual(self.bot.state['cooldown_until']-self.ex.now(),60)
            self.tick();self.restart();self.tick()
            self.assertEqual(self.messages,[expected])

        def partial_entry_tp(self):
            e=self.seed();self.ex.auto_market=True
            self.ex.fill(e['order_id'],'0.025');self.tick()
            tp=self.bot.active(PAIR[0],{'T'})[0]
            self.assertEqual(dec(tp['body']['quantity']),dec('0.025'))
            return e,tp

        def test_76_full_btc_entry_replaces_partial_tp_with_one_whole_tp(self):
            e,old=self.partial_entry_tp()
            self.ex.fill(e['order_id'],'0.0375');self.tick()
            self.assertTrue(self.bot.state['orders'][old['body']['clientId']]['cancel_requested'])
            self.tick()
            active=self.bot.active(PAIR[0],{'T'})
            self.assertEqual(len(active),1)
            self.assertNotEqual(active[0]['body']['clientId'],old['body']['clientId'])
            self.assertEqual(dec(active[0]['body']['quantity']),dec('0.0625'))
            self.assertEqual(dec(active[0]['body']['price']),self.bot.tp_target(PAIR[0]))
            self.assertTrue(active[0]['body']['reduceOnly'])
            count=len(self.ex.placed);self.restart();self.tick()
            self.assertEqual(len(self.ex.placed),count)

        def test_77_whole_tp_waits_for_confirmed_cancel(self):
            e,old=self.partial_entry_tp();self.ex.cancel_pending=True
            self.ex.fill(e['order_id'],'0.0375');self.tick();self.tick()
            btc_tps=[r for r in self.ex.placed if r['marketId']==1 and '_T' in r['clientId']]
            self.assertEqual(len(btc_tps),1)
            self.assertEqual(self.bot.active(PAIR[0],{'T'})[0]['body']['clientId'],old['body']['clientId'])
            self.ex.cancel_pending=False;self.ex.t+=self.ex.cfg['cancel_retry_sec']+1
            self.tick();self.tick()
            active=self.bot.active(PAIR[0],{'T'})
            self.assertEqual(len(active),1)
            self.assertEqual(dec(active[0]['body']['quantity']),dec('0.0625'))

        def test_78_tp_fill_during_consolidation_still_flattens_all(self):
            e,old=self.partial_entry_tp()
            self.ex.fill(e['order_id'],'0.0375')
            original=self.ex.cancel
            def racing(rec):
                if rec['body']['clientId']==old['body']['clientId'] and not order_terminal(self.ex.rows[rec['order_id']]):
                    self.ex.fill(rec['order_id'],'0.01',rec['body']['price'])
                original(rec)
            with patch.object(self.ex,'cancel',side_effect=racing):
                try:self.tick()
                except SafetyError as exc:self.assertIn('真实仓位变化',str(exc))
            self.tick();self.tick()
            self.assertEqual(self.bot.state['state'],'WAIT')
            self.assertFalse(self.ex.positions);self.assertFalse(self.ex.open_orders())
            btc_tps=[r for r in self.ex.placed if r['marketId']==1 and '_T' in r['clientId']]
            self.assertEqual(len(btc_tps),1)  # No new whole TP after the exit gate.

        def test_79_existing_split_tps_consolidate_after_restart(self):
            self.fill_btc();self.ex.auto_market=True;self.bot.hedge_tick();self.bot.reconcile()
            price=self.bot.tp_target(PAIR[0])
            self.bot.submit(PAIR[0],'T','SELL',dec('0.025'),price,reduce=True)
            self.bot.submit(PAIR[0],'T','SELL',dec('0.0375'),price,reduce=True)
            self.restart();self.tick();self.tick()
            active=self.bot.active(PAIR[0],{'T'})
            self.assertEqual(len(active),1)
            self.assertEqual(dec(active[0]['body']['quantity']),abs(self.bot.qty(PAIR[0])))

        def test_80_fast_hedge_poll_preserves_normal_scan(self):
            self.assertEqual(self.ex.cfg['scan_interval_sec'],30)
            self.assertEqual(self.bot.next_scan_interval(),30)
            e=self.seed()
            self.assertEqual(self.bot.next_scan_interval(),5)
            self.ex.fill(e['order_id'],e['body']['quantity']);self.bot.reconcile()
            self.assertEqual(self.bot.next_scan_interval(),5)
            self.bot.hedge_tick()
            self.assertEqual(self.bot.next_scan_interval(),5)
            h=self.bot.active(PAIR[1],{'H'})[0]
            self.ex.fill(h['order_id'],h['body']['quantity']);self.bot.reconcile()
            self.assertEqual(self.bot.next_scan_interval(),30)
            self.bot.tp_tick(PAIR[0]);self.bot.tp_tick(PAIR[1])
            self.assertEqual(self.bot.next_scan_interval(),30)

        def test_81_partial_btc_and_eth_keep_fast_poll(self):
            e=self.seed();self.ex.fill(e['order_id'],'0.025');self.bot.reconcile()
            self.bot.hedge_tick();h=self.bot.active(PAIR[1],{'H'})[0]
            self.ex.fill(h['order_id'],'0.2',terminal=True);self.bot.reconcile()
            self.assertEqual(self.bot.next_scan_interval(),5)
            self.ex.cancel(e);self.bot.reconcile()
            self.assertEqual(self.bot.next_scan_interval(),5)
            self.ex.auto_market=True;self.bot.hedge_tick();self.bot.reconcile()
            self.assertEqual(self.bot.next_scan_interval(),30)

        def test_82_dust_and_exit_do_not_change_normal_poll(self):
            self.legs(True)
            self.assertGreater(self.bot.notionals()[0]-self.bot.notionals()[1],0)
            self.assertEqual(self.bot.next_scan_interval(),30)
            self.bot.begin_exit('测试')
            self.assertEqual(self.bot.next_scan_interval(),30)

        def test_83_fast_poll_configuration_and_no_mutations(self):
            before=copy.deepcopy(self.bot.state)
            for _ in range(3):self.bot.next_scan_interval()
            self.assertEqual(self.bot.state,before);self.assertFalse(self.ex.placed)
            for value in (0,-1,True,'5',float('nan')):
                bad=copy.deepcopy(cfg);bad['hedge_scan_interval_sec']=value
                with self.assertRaises(ValueError):validate_config(bad)

    # The paired strategy no longer places per-leg T orders. Retain the old
    # single-leg/grid tests for historical coverage, but do not treat them as
    # requirements for the new portfolio-exit contract.
    _legacy_pair_tp_tests = {
        'test_07_btc_tp_flattens_all','test_08_eth_tp_flattens_all',
        'test_10_restart_existing_legs_no_duplicate','test_14_partial_tp_also_flattens_both',
        'test_26_pending_entry_fill_during_cancel_also_closed',
        'test_30_tp_exit_gate_survives_account_failure_and_restart',
        'test_35_tp_reprices_after_real_average_changes',
        'test_43_tp_during_hedge_submission_blocks_new_exposure',
        'test_59_persisted_wait_restart_adopts_both_real_sides',
        'test_60_live_wait_adopts_without_rsi_or_new_btc',
        'test_63_adopted_quantity_increase_refreshes_tp_no_duplicate_hedge',
        'test_64_same_quantity_new_real_average_updates_basis_and_tp',
        'test_70_adopted_tp_flattens_and_cools_exactly_sixty_seconds',
        'test_73_reversed_external_pair_replaces_wrong_direction_tp',
        'test_76_full_btc_entry_replaces_partial_tp_with_one_whole_tp',
        'test_77_whole_tp_waits_for_confirmed_cancel',
        'test_78_tp_fill_during_consolidation_still_flattens_all',
        'test_79_existing_split_tps_consolidate_after_restart',
    }
    for _name in _legacy_pair_tp_tests:
        if hasattr(Tests, _name):
            setattr(Tests, _name, unittest.skip('旧版单腿T止盈测试；组合止盈v1.1不挂单腿T订单')(getattr(Tests, _name)))

    def _test_pair_no_single_leg_tp(self):
        self.legs()
        self.assertFalse(self.bot.active(roles={'T'}))
    def _test_pair_profit_target(self):
        self.legs(); self.ex.prices[PAIR[0]]=dec('80560'); self.ex.prices[PAIR[1]]=dec('3972')
        reason=self.bot.pair_risk_trigger()
        self.assertIn('止盈', reason or '')
    def _test_single_leg_profit_not_pair_profit(self):
        self.legs(); self.ex.prices[PAIR[0]]=dec('80640'); self.ex.prices[PAIR[1]]=dec('4040')
        self.assertIsNone(self.bot.pair_risk_trigger())
    def _test_pair_timeout(self):
        self.legs(); self.ex.t += self.ex.cfg['pair_max_hold_seconds']
        self.assertIn('超时', self.bot.pair_risk_trigger() or '')
    Tests.test_84_pair_has_no_single_leg_tp = _test_pair_no_single_leg_tp
    Tests.test_85_pair_profit_target = _test_pair_profit_target
    Tests.test_86_single_leg_profit_is_not_pair_profit = _test_single_leg_profit_not_pair_profit
    Tests.test_87_pair_timeout = _test_pair_timeout

    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__=='__main__':
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        log('STOP',reason='已停止；保留状态，未自动撤单或平仓')
    except SafetyError as exc:
        log('STOP',reason=str(exc))
        sys.exit(2)
