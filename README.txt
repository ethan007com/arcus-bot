Arcus BTC/ETH 对冲机器人 使用说明

【环境】
Python 3.10 以上（作者在 3.14 上运行）
安装依赖：pip install -r requirements.txt

【填写账户】（二选一）
1. 直接写进 config.json：
   wallet_address  = 你的 Arcus 钱包地址（0x 开头）
   api_signing_key = Arcus 后台生成的 API Signing Key（Ed25519，不是钱包私钥！）
2. 或者用环境变量（更安全，config 里留空即可）：
   export ARCUS_WALLET_ADDRESS=0x...
   export ARCUS_SIGNING_KEY=...
可选 Telegram 通知：export ARCUS_TELEGRAM_BOT_TOKEN=...  ARCUS_TELEGRAM_CHAT_ID=...
   （不用的话把 config 里 telegram_enabled 改成 false）

account_index = 交易的子账户编号（0 是主账户）。API Key 必须是在同一个子账户下创建的。

【运行】
python -u bot.py
默认 dry_run=true，只看信号不下单。确认日志正常后再改成 false 实盘。

【策略】
BTC 5 分钟 RSI12 < 45 做多 BTC，> 55 做空 BTC；
同时开等额反向 ETH 对冲；BTC 涨跌 0.8% 止盈，两边一起平。
BTC 40 倍、ETH 25 倍全仓（需先在交易所把杠杆和全仓模式设好，不一致会拒绝启动）。
每边名义金额 ≈ 账户权益 × 5。

【注意】
- 建议单独开一个子账户只给机器人用，不要在这个账户手动下单，否则会因“未登记挂单”自动停机。
- 运行后会生成 runtime 文件夹（账本），重启靠它恢复，不要删。
- 中国大陆/美国等地区 IP 可能被交易所拒绝（GEO_RESTRICTED）。
- 实盘有爆仓风险，先用小资金测试。
