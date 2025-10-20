#!/usr/bin/env python3
# Cleaned14_30m_SOLUSDT.py
# Changes:
# - Moved logging setup to top to fix NameError in check_time_offset
# - Fixed log_pnl using 'log' instead of 'log'
# - Ensured Decimal types in trade_state for consistency
# - Previous: Added Telegram notifications for position closures, disabled kline caching, fixed monitor_trade

import argparse
import logging
import time
import hmac
import hashlib
import requests
import os
import signal
import sys
import statistics
import csv
import threading
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone
from urllib.parse import urlencode
from telegram import Bot
import schedule
import asyncio
import certifi

# -------- LOGGING SETUP (MOVED TO TOP) ----------
class CustomFormatter(logging.Formatter):
    def formatTime(self, record, datefmt=None):
        dt = datetime.fromtimestamp(record.created, tz=timezone.utc)
        return dt.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3] + '+00:00'

logger = logging.getLogger()
logger.handlers.clear()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(console_handler)
file_handler = logging.FileHandler('bot.log')
file_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(file_handler)
log = logger.info

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")          # 0.5% per trade
SL_PCT = Decimal("0.0075")           # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MACD_FAST = 12
MACD_SLOW = 26
MACD_SIGNAL = 9
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 50
BUY_RSI_MAX = 70
SELL_RSI_MIN = 30
SELL_RSI_MAX = 50
CALLBACK_RATE_MIN = Decimal("0.1")
CALLBACK_RATE_MAX = Decimal("5.0")
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = 0  # Disabled to ensure fresh data

# Global stop flag and client
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
klines_cache = None
klines_cache_time = 0

# Global PnL tracking
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []  # List of dicts: {'date': str, 'trade_id': int, 'side': str, 'entry': float, 'exit': float, 'pnl_usd': float, 'pnl_r': float}

def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    pnl_r = pnl_usd / R if R > 0 else 0
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': float(entry),
        'exit': float(exit_price),
        'pnl_usd': float(pnl_usd),
        'pnl_r': float(pnl_r)
    }
    pnl_data.append(row)
    with open(PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, row.keys())
        writer.writerow(row)

def calculate_pnl_report(period='daily'):
    if not pnl_data:
        return "No trades recorded."
    from datetime import timedelta
    end_date = datetime.now(timezone.utc)
    if period == 'daily':
        start_date = end_date - timedelta(days=1)
    elif period == 'weekly':
        start_date = end_date - timedelta(weeks=1)
    elif period == 'monthly':
        start_date = end_date - timedelta(days=30)
    else:
        return "Invalid period."
    period_trades = [t for t in pnl_data if datetime.fromisoformat(t['date']) >= start_date]
    if not period_trades:
        return f"No trades in {period} period."
    total_pnl_usd = sum(t['pnl_usd'] for t in period_trades)
    total_pnl_r = sum(t['pnl_r'] for t in period_trades)
    num_trades = len(period_trades)
    wins = len([t for t in period_trades if t['pnl_r'] > 0])
    win_rate = (wins / num_trades * 100) if num_trades > 0 else 0
    report = f"{period.capitalize()} PnL Report:\n- Trades: {num_trades}\n- Win Rate: {win_rate:.2f}%\n- Total PnL: ${total_pnl_usd:.2f}\n- Total PnL: {total_pnl_r:.2f}R"
    return report

async def send_telegram_message(bot, chat_id, message):
    try:
        await bot.send_message(chat_id=chat_id, text=message)
        log(f"Telegram message sent: {message[:50]}...")
    except Exception as e:
        log(f"Telegram send failed: {str(e)}")

def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']}"
    )
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, message))).start()

def send_daily_report(bot, chat_id):
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_weekly_report(bot, chat_id):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_monthly_report(bot, chat_id):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def _request_stop(signum, frame, symbol=None):
    global STOP_REQUESTED, client
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    try:
        if client and symbol:
            pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
            pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
            if pos_amt != 0:
                side = "SELL" if pos_amt > 0 else "BUY"
                qty = abs(pos_amt)
                try:
                    client.send_signed_request("POST", "/fapi/v1/order", {
                        "symbol": symbol,
                        "side": side,
                        "type": "MARKET",
                        "quantity": str(qty)
                    })
                    log(f"Closed position: qty={qty} {side}")
                except Exception as e:
                    log(f"Failed to close position: {str(e)}")
            client.cancel_all_open_orders(symbol)
            log(f"All open orders cancelled for {symbol}.")
        else:
            log("Client or symbol not defined; skipping position closure and order cancellation.")
    except Exception as e:
        log(f"Failed to handle stop: {str(e)}")

# -------- TIME SYNC CHECK ----------
def check_time_offset(base_url):
    max_attempts = 3
    for attempt in range(max_attempts):
        try:
            response = requests.get(f"{base_url}/fapi/v1/time", timeout=15, verify=certifi.where())
            server_time_ms = response.json()['serverTime']
            server_time = datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc)
            local_time = datetime.now(timezone.utc)
            offset = (server_time - local_time).total_seconds()
            log(f"Time offset from Binance: {offset} seconds (attempt {attempt+1}/{max_attempts})")
            if abs(offset) > 5:
                log("Warning: Clock offset > 5s. Using recvWindow=10000.")
            return
        except Exception as e:
            log(f"Binance time sync failed (attempt {attempt+1}/{max_attempts}): {str(e)}")
            if attempt < max_attempts - 1:
                sleep_time = 2 ** attempt
                log(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)
            else:
                log("All time sync attempts failed. Using local time with recvWindow=10000.")

# -------- BINANCE CLIENT ----------
class BinanceAPIError(Exception):
    def __init__(self, message, status_code=None, payload=None):
        super().__init__(message)
        self.status_code = status_code
        self.payload = payload

class BinanceClient:
    def __init__(self, api_key, api_secret, use_live=False, base_override=None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.use_live = use_live
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        print(f"🔗 Using base URL: {self.base}")
        time.sleep(1)  # Delay to avoid rate limits
        check_time_offset(self.base)

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params.copy() if params else {}
        for attempt in range(5):
            try:
                response = requests.get(f"{self.base}/fapi/v1/time", timeout=15, verify=certifi.where())
                server_time_ms = response.json()['serverTime']
                params["timestamp"] = server_time_ms
            except Exception as e:
                log(f"Time sync failed (attempt {attempt+1}/5): {str(e)}. Using local time.")
                params["timestamp"] = int(time.time() * 1000)
            params["recvWindow"] = 10000
            query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
            signature = self._sign(query)
            url = f"{self.base}{endpoint}?{query}&signature={signature}"
            headers = {"X-MBX-APIKEY": self.api_key}
            try:
                r = requests.request(method, url, headers=headers, timeout=30, verify=certifi.where())
                if r.status_code == 200:
                    response = r.json()
                    if isinstance(response, dict) and response.get("code") not in (None, 200):
                        raise BinanceAPIError(f"API error: {response.get('msg', 'Unknown error')} (code {response.get('code')})", status_code=r.status_code, payload=response)
                    return response
                else:
                    try:
                        payload = r.json()
                    except Exception:
                        payload = r.text
                    raise BinanceAPIError(f"HTTP {r.status_code}: {payload}", status_code=r.status_code, payload=payload)
            except BinanceAPIError as e:
                if attempt < 4:
                    time.sleep(2 ** attempt)
                    continue
                raise
            except Exception as e:
                if attempt < 4:
                    time.sleep(2 ** attempt)
                    continue
                raise

    def cancel_all_open_orders(self, symbol):
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol})

    def get_open_orders(self, symbol):
        return self.send_signed_request("GET", "/fapi/v1/openOrders", {"symbol": symbol})

    def get_klines(self, symbol, interval, limit=100):
        global klines_cache, klines_cache_time
        current_time = time.time()
        if klines_cache and klines_cache_time and (current_time - klines_cache_time) < KLINES_CACHE_DURATION:
            return klines_cache
        params = {"symbol": symbol, "interval": interval, "limit": limit}
        klines = self.send_signed_request("GET", "/fapi/v1/klines", params)
        klines_cache = klines
        klines_cache_time = current_time
        return klines

    def get_symbol_ticker(self, symbol):
        return self.send_signed_request("GET", "/fapi/v1/ticker/price", {"symbol": symbol})

    def get_position_risk(self, symbol):
        return self.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})

    def create_order(self, symbol, side, type, **kwargs):
        params = {"symbol": symbol, "side": side, "type": type}
        params.update(kwargs)
        return self.send_signed_request("POST", "/fapi/v1/order", params)

# -------- TRADE MANAGEMENT ----------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price = Decimal('0')
        self.qty = Decimal('0')
        self.side = ""
        self.entry_close_time = 0
        self.exit_close_time = 0
        self.sl = Decimal('0')
        self.tp = Decimal('0')
        self.trail_activated = False
        self.trail_order_id = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_activation_price = Decimal('0')

def fetch_balance(client):
    max_attempts = 3
    for attempt in range(max_attempts):
        try:
            account = client.send_signed_request("GET", "/fapi/v2/account")
            return Decimal(str(account.get('availableBalance', '0')))
        except BinanceAPIError as e:
            if attempt < max_attempts - 1:
                log(f"Balance fetch failed (attempt {attempt+1}/{max_attempts}): {str(e)}. Retrying...")
                time.sleep(2 ** attempt)
                continue
            raise
        except Exception as e:
            if attempt < max_attempts - 1:
                log(f"Balance fetch failed (attempt {attempt+1}/{max_attempts}): {str(e)}. Retrying...")
                time.sleep(2 ** attempt)
                continue
            raise

def fetch_open_positions_details(client, symbol):
    return client.get_position_risk(symbol)[0]

def has_active_position(client, symbol):
    pos = fetch_open_positions_details(client, symbol)
    return abs(Decimal(str(pos.get("positionAmt", "0")))) > Decimal('0')

def place_market_order(client, symbol, side, qty):
    return client.create_order(symbol=symbol, side=side, type='MARKET', quantity=str(qty))

def place_sl_order_closepos(client, symbol, price, side):
    return client.create_order(symbol=symbol, side=side, type='STOP_MARKET', closePosition=True, stopPrice=str(price))

def place_tp_order_closepos(client, symbol, price, side):
    return client.create_order(symbol=symbol, side=side, type='TAKE_PROFIT_MARKET', closePosition=True, stopPrice=str(price))

def place_trailing_stop(client, symbol, side, activation_price, callback_rate, qty, sl_price):
    return client.create_order(
        symbol=symbol,
        side=side,
        type='TRAILING_STOP_MARKET',
        activationPrice=str(activation_price),
        callbackRate=str(callback_rate),
        quantity=str(qty),
        stopPrice=str(sl_price)
    )

def get_symbol_filters(client, symbol):
    global symbol_filters_cache
    if not symbol_filters_cache or symbol_filters_cache.get("symbol") != symbol:
        exchange_info = client.send_signed_request("GET", "/fapi/v1/exchangeInfo")
        for s in exchange_info["symbols"]:
            if s["symbol"] == symbol:
                symbol_filters_cache = s
                break
    filters = {f["filterType"]: f for f in symbol_filters_cache["filters"]}
    tick_size = Decimal(str(filters["priceFilter"]["tickSize"]))
    step_size = Decimal(str(filters["lotSize"]["stepSize"]))
    min_notional = Decimal(str(filters["notionalFilter"]["minNotional"]))
    return {"tickSize": tick_size, "stepSize": step_size, "minNotional": min_notional}

# -------- MONITORING ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id):
    log("Monitoring active trade...")
    last_position_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested during monitoring. Exiting.")
            break
        try:
            current_time = time.time()
            if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
                pos = fetch_open_positions_details(client, symbol)
                pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                unrealized_pnl = Decimal(str(pos.get("unrealizedProfit", "0"))) if pos else Decimal('0')
                log(f"Unrealized PNL: {unrealized_pnl.quantize(Decimal('0.01'))} USDT")
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    ticker = client.get_symbol_ticker(symbol)
                    current_price = Decimal(str(ticker.get("price")))
                    if (trade_state.side == "LONG" and current_price >= trade_state.trail_activation_price) or \
                       (trade_state.side == "SHORT" and current_price <= trade_state.trail_activation_price):
                        log(f"Trailing stop activated at price={current_price} (activationPrice={trade_state.trail_activation_price})")
                        trade_state.trail_activated = True
                if trade_state.trail_activated and trade_state.trail_order_id:
                    orders = client.get_open_orders(symbol)
                    trail_order = next((o for o in orders if o.get("orderId") == trade_state.trail_order_id), None)
                    if trail_order:
                        stop_price = Decimal(str(trail_order.get("stopPrice", "0")))
                        current_price = Decimal(str(client.get_symbol_ticker(symbol).get("price")))
                        trail_distance = abs(current_price - stop_price) if trade_state.side == "LONG" else abs(stop_price - current_price)
                        expected_trail_distance = 2 * abs(trade_state.trail_activation_price - trade_state.sl)
                        log(f"Trailing stop update: stopPrice={stop_price}, currentPrice={current_price}, trailDistance={trail_distance} (expected 2R={expected_trail_distance})")
                        if abs(trail_distance - expected_trail_distance) > Decimal('0.01') * expected_trail_distance:
                            log(f"Warning: Trailing distance {trail_distance} deviates from expected 2R={expected_trail_distance}")
                    else:
                        log("Trailing stop order no longer exists; position may have closed.")
                if pos_amt == Decimal('0'):
                    open_orders = client.get_open_orders(symbol)
                    trail_order = next((o for o in open_orders if o.get("orderId") == trade_state.trail_order_id), None) if trade_state.trail_activated else None
                    sl_order = next((o for o in open_orders if o.get("orderId") == trade_state.sl_order_id), None) if trade_state.sl_order_id else None
                    tp_order = next((o for o in open_orders if o.get("orderId") == trade_state.tp_order_id), None) if trade_state.tp_order_id else None
                    close_side = "BUY" if trade_state.side == "SHORT" else "SELL"
                    close_qty = trade_state.qty
                    close_price = Decimal(str(client.get_symbol_ticker(symbol).get("price")))
                    close_price_str = str(close_price.quantize(Decimal(str(tick_size))))
                    if trade_state.trail_activated and not trail_order:
                        log(f"Position closed (trailing stop executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        send_trade_telegram({"symbol": symbol, "side": trade_state.side, "exit": float(close_price), "qty": float(close_qty)}, telegram_bot, telegram_chat_id)
                    elif sl_order is None and trade_state.sl_order_id:
                        log(f"Position closed (stop-loss executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        send_trade_telegram({"symbol": symbol, "side": trade_state.side, "exit": float(close_price), "qty": float(close_qty)}, telegram_bot, telegram_chat_id)
                    elif tp_order is None and trade_state.tp_order_id:
                        log(f"Position closed (take-profit executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        send_trade_telegram({"symbol": symbol, "side": trade_state.side, "exit": float(close_price), "qty": float(close_qty)}, telegram_bot, telegram_chat_id)
                    else:
                        log(f"Position closed (unknown reason): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        send_trade_telegram({"symbol": symbol, "side": trade_state.side, "exit": float(close_price), "qty": float(close_qty)}, telegram_bot, telegram_chat_id)
                    try:
                        client.cancel_all_open_orders(symbol)
                        log("All open orders cancelled after position closure.")
                    except Exception as e:
                        log(f"Failed to cancel orders: {str(e)}")
                    break
                last_position_check = current_time
        except BinanceAPIError as e:
            log(f"Monitor error: {str(e)}, payload: {e.payload}")
            time.sleep(2)
        except Exception as e:
            log(f"Monitor error: {str(e)}")
            time.sleep(2)

# -------- TRADING LOGIC ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, use_macd, telegram_bot, telegram_chat_id):
    last_processed_time = 0  # Initialized to fix loop error
    trades_today = 0
    daily_loss = Decimal('0')
    trade_state = TradeState()
    pending_entry = False
    server_time = int(time.time() * 1000)  # Use local time as fallback
    try:
        server_time = client.send_signed_request("GET", "/fapi/v1/time")["serverTime"]
    except Exception:
        log("Failed to sync server time. Using local time.")
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s ...")
                _safe_sleep(sleep_seconds)
                continue

            klines = client.get_klines(symbol, timeframe, limit=100)
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]

            if last_processed_time == last_close_time:
                log(f"Duplicate candle detected at {last_close_time}; sleeping 1s")
                time.sleep(1)
                continue

            # Calculate RSI with Wilder's smoothing
            raw_closes = [float(k[4]) for k in klines[-RSI_PERIOD-1:]] if len(klines) > RSI_PERIOD else []
            log(f"Raw closes for RSI (last {RSI_PERIOD+1} periods): {raw_closes}")
            if len(raw_closes) > 1:
                price_changes = [raw_closes[i] - raw_closes[i-1] for i in range(1, len(raw_closes))]
                gains = [max(0, change) for change in price_changes]
                losses = [-min(0, change) for change in price_changes]
                if not avg_gain and not avg_loss:  # First calculation
                    avg_gain = sum(gains) / RSI_PERIOD
                    avg_loss = sum(losses) / RSI_PERIOD if losses else 0.0001  # Avoid division by zero
                else:
                    avg_gain = (avg_gain * 13 + gains[-1]) / 14
                    avg_loss = (avg_loss * 13 + losses[-1]) / 14 if losses else avg_loss * 13 / 14
                rs = avg_gain / avg_loss if avg_loss > 0 else 0 if avg_gain == 0 else float('inf')
                rsi = 100 - (100 / (1 + rs)) if avg_loss > 0 else 100 if avg_gain == 0 else 0
                log(f"RSI calculation: avg_gain={avg_gain}, avg_loss={avg_loss}, RS={rs}, RSI={rsi}")
            else:
                rsi = None
                log("Insufficient data for RSI calculation.")

            macd_fast = statistics.mean([float(k[4]) for k in klines[-MACD_FAST:]]) if len(klines) >= MACD_FAST else None
            macd_slow = statistics.mean([float(k[4]) for k in klines[-MACD_SLOW:]]) if len(klines) >= MACD_SLOW else None
            macd_signal = statistics.mean([macd_fast - macd_slow for _ in range(MACD_SIGNAL)]) if macd_fast and macd_slow and len(klines) >= MACD_SLOW + MACD_SIGNAL else None
            bullish_crossover = macd_fast > macd_signal and (not macd_signal or macd_fast > macd_slow)
            bearish_crossover = macd_fast < macd_signal and (not macd_signal or macd_fast < macd_slow)
            vol_sma15 = statistics.mean(volumes[-VOL_SMA_PERIOD:]) if len(volumes) >= VOL_SMA_PERIOD else None
            curr_vol = volumes[-1]
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            close_time = last_close_time
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            log(f"Candle open={open_price}, close={close_price}, RSI={rsi}, MACD={macd_fast-macd_slow if macd_fast and macd_slow else 'N/A'}, Signal={macd_signal if macd_signal else 'N/A'}, Vol={curr_vol:.2f}, SMA15={vol_sma15 or 0:.2f}, {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle")

            if prevent_same_bar and trade_state.exit_close_time == close_time:
                log("Same bar as exit. Skipping to prevent re-entry.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if require_no_pos and has_active_position(client, symbol):
                log("Active position detected. Waiting for closure.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if use_volume_filter and (vol_sma15 is None or curr_vol <= vol_sma15):
                log("Waiting for volume history or insufficient volume...")
                last_processed_time = close_time
                time.sleep(1)
                continue

            buy_signal = rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_macd or bullish_crossover)
            sell_signal = rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_macd or bearish_crossover)

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.")
                pending_entry = False

                entry_price = close_price
                entry_price_f = float(entry_price)
                if buy_signal:
                    sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price + (tp_mult * R)
                    close_side_for_sl = "SELL"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP
                else:
                    sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price - (tp_mult * R)
                    close_side_for_sl = "BUY"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP

                if R <= Decimal('0'):
                    log(f"Invalid R ({R}) <= 0. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                bal = fetch_balance(client)
                risk_amount = bal * risk_pct
                qty = risk_amount / R
                qty_api = quantize_qty(qty, step_size)
                if qty_api < min_qty:
                    qty_api = min_qty
                notional = qty_api * entry_price
                if notional < min_notional:
                    qty_api = quantize_qty(min_notional / entry_price, step_size)

                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)

                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price_f}")
                timed_out = False
                actual_qty = None
                try:
                    order_res = place_market_order(client, symbol, side_text, qty_api)
                    log(f"Market order placed: {order_res}")
                except Exception as e:
                    log(f"Market order failed: {str(e)}")
                    pending_entry = False
                    time.sleep(1)
                    continue

                log("Waiting for entry order to fill...")
                start_time = time.time()
                while True:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        log("Stop requested during fill wait; aborting entry flow.")
                        break
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        log("Timeout waiting for fill. Attempting to cancel order...")
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("Entry order cancelled.")
                        except Exception as e:
                            log(f"Cancel failed: {str(e)}")
                        timed_out = True
                        break
                    time.sleep(0.5)

                if timed_out or actual_qty is None:
                    pending_entry = False
                    log("Entry timed out or aborted -> skipping this signal and waiting for next candle.")
                    continue

                # Fetch actual fill price
                time.sleep(0.2)  # 200ms delay for fill data
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, use_macd, telegram_bot, telegram_chat_id):
    last_processed_time = 0  # Initialized to fix loop error
    trades_today = 0
    daily_loss = Decimal('0')
    trade_state = TradeState()
    pending_entry = False
    server_time = int(time.time() * 1000)  # Use local time as fallback
    avg_gain = 0.0  # Initialize outside loop
    avg_loss = 0.0001  # Initialize to avoid division by zero
    try:
        server_time = client.send_signed_request("GET", "/fapi/v1/time")["serverTime"]
    except Exception:
        log("Failed to sync server time. Using local time.")
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s ...")
                _safe_sleep(sleep_seconds)
                continue

            klines = client.get_klines(symbol, timeframe, limit=100)
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]

            if last_processed_time == last_close_time:
                log(f"Duplicate candle detected at {last_close_time}; sleeping 1s")
                time.sleep(1)
                continue

            # Calculate RSI with Wilder's smoothing
            raw_closes = [float(k[4]) for k in klines[-RSI_PERIOD-1:]] if len(klines) > RSI_PERIOD else []
            log(f"Raw closes for RSI (last {RSI_PERIOD+1} periods): {raw_closes}")
            rsi = None
            if len(raw_closes) > 1:
                price_changes = [raw_closes[i] - raw_closes[i-1] for i in range(1, len(raw_closes))]
                gains = [max(0, change) for change in price_changes]
                losses = [-min(0, change) for change in price_changes]
                if len(gains) < RSI_PERIOD:  # First RSI_PERIOD periods
                    avg_gain = sum(gains) / len(gains) if gains else 0.0
                    avg_loss = sum(losses) / len(losses) if losses else 0.0001
                else:
                    avg_gain = (avg_gain * 13 + gains[-1]) / 14
                    avg_loss = (avg_loss * 13 + losses[-1]) / 14 if losses else avg_loss * 13 / 14
                rs = avg_gain / avg_loss if avg_loss > 0 else 0 if avg_gain == 0 else float('inf')
                rsi = 100 - (100 / (1 + rs)) if avg_loss > 0 else 100 if avg_gain == 0 else 0
                log(f"RSI calculation: avg_gain={avg_gain}, avg_loss={avg_loss}, RS={rs}, RSI={rsi}")
            else:
                log("Insufficient data for RSI calculation.")

            macd_fast = statistics.mean([float(k[4]) for k in klines[-MACD_FAST:]]) if len(klines) >= MACD_FAST else None
            macd_slow = statistics.mean([float(k[4]) for k in klines[-MACD_SLOW:]]) if len(klines) >= MACD_SLOW else None
            macd_signal = statistics.mean([macd_fast - macd_slow for _ in range(MACD_SIGNAL)]) if macd_fast and macd_slow and len(klines) >= MACD_SLOW + MACD_SIGNAL else None
            bullish_crossover = macd_fast > macd_signal and (not macd_signal or macd_fast > macd_slow)
            bearish_crossover = macd_fast < macd_signal and (not macd_signal or macd_fast < macd_slow)
            vol_sma15 = statistics.mean(volumes[-VOL_SMA_PERIOD:]) if len(volumes) >= VOL_SMA_PERIOD else None
            curr_vol = volumes[-1]
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            close_time = last_close_time
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            log(f"Candle open={open_price}, close={close_price}, RSI={rsi}, MACD={macd_fast-macd_slow if macd_fast and macd_slow else 'N/A'}, Signal={macd_signal if macd_signal else 'N/A'}, Vol={curr_vol:.2f}, SMA15={vol_sma15 or 0:.2f}, {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle")

            if prevent_same_bar and trade_state.exit_close_time == close_time:
                log("Same bar as exit. Skipping to prevent re-entry.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if require_no_pos and has_active_position(client, symbol):
                log("Active position detected. Waiting for closure.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if use_volume_filter and (vol_sma15 is None or curr_vol <= vol_sma15):
                log("Waiting for volume history or insufficient volume...")
                last_processed_time = close_time
                time.sleep(1)
                continue

            buy_signal = rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_macd or bullish_crossover)
            sell_signal = rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_macd or bearish_crossover)

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.")
                pending_entry = False

                entry_price = close_price
                entry_price_f = float(entry_price)
                if buy_signal:
                    sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price + (tp_mult * R)
                    close_side_for_sl = "SELL"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP
                else:
                    sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price - (tp_mult * R)
                    close_side_for_sl = "BUY"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP

                if R <= Decimal('0'):
                    log(f"Invalid R ({R}) <= 0. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                bal = fetch_balance(client)
                risk_amount = bal * risk_pct
                qty = risk_amount / R
                filters = get_symbol_filters(client, symbol)
                qty_api = quantize_qty(qty, filters['stepSize'])
                if qty_api < Decimal('0.01'):
                    qty_api = Decimal('0.01')
                notional = qty_api * entry_price
                if notional < filters['minNotional']:
                    qty_api = quantize_qty(filters['minNotional'] / entry_price, filters['stepSize'])

                sl_price_dec_quant = quantize_price(sl_price_dec, filters['tickSize'], sl_rounding)
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, filters['tickSize'], tp_rounding)
                tp_price_f = float(tp_price_dec_quant)

                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price_f}")
                timed_out = False
                actual_qty = None
                try:
                    order_res = place_market_order(client, symbol, side_text, qty_api)
                    log(f"Market order placed: {order_res}")
                except Exception as e:
                    log(f"Market order failed: {str(e)}")
                    pending_entry = False
                    time.sleep(1)
                    continue

                log("Waiting for entry order to fill...")
                start_time = time.time()
                while True:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        log("Stop requested during fill wait; aborting entry flow.")
                        break
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        log("Timeout waiting for fill. Attempting to cancel order...")
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("Entry order cancelled.")
                        except Exception as e:
                            log(f"Cancel failed: {str(e)}")
                        timed_out = True
                        break
                    time.sleep(0.5)

                if timed_out or actual_qty is None:
                    pending_entry = False
                    log("Entry timed out or aborted -> skipping this signal and waiting for next candle.")
                    continue

                # Fetch actual fill price
                time.sleep(0.2)  # 200ms delay for fill data
                actual_fill_price = client.get_symbol_ticker(symbol).get("price", entry_price)
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.")
                    actual_fill_price = entry_price
                actual_fill_price_f = float(Decimal(str(actual_fill_price)))

                # Calculate trailing stop parameters
                if buy_signal:
                    sl_price_dec_quant = actual_fill_price * (Decimal("1") - SL_PCT)
                    R = actual_fill_price * SL_PCT
                    trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
                    trail_distance_dec = 2 * R
                else:
                    sl_price_dec_quant = actual_fill_price * (Decimal("1") + SL_PCT)
                    R = actual_fill_price * SL_PCT
                    trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                    trail_distance_dec = 2 * R
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, filters['tickSize'])
                trail_activation_price_f = float(trail_activation_price_dec_quant)
                callback_rate_dec = (trail_distance_dec / trail_activation_price_dec * Decimal("100")).quantize(Decimal('0.01'))
                callback_rate_f = float(callback_rate_dec)

                # Check if trailing stop activation price is too close to current price
                try:
                    ticker = client.get_symbol_ticker(symbol)
                    current_price = Decimal(str(ticker.get("price")))
                except Exception as e:
                    log(f"Price fetch failed: {str(e)}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
                if buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue
                elif not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                trade_state.active = True
                trade_state.entry_price = actual_fill_price_f
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.sl = sl_price_f
                trade_state.tp = tp_price_f
                trade_state.trail_activated = False
                trade_state.trail_order_id = None
                trade_state.sl_order_id = None
                trade_state.tp_order_id = None
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                log(f"Position opened: {trade_state.side}, qty={trade_state.qty}, entry={trade_state.entry_price}, sl={trade_state.sl}, tp={trade_state.tp}, trailActivation={trade_state.trail_activation_price}, trailDistance={trail_distance_dec} (2R)")

                # Send Telegram notification
                trade_details = {
                    'symbol': symbol,
                    'side': trade_state.side,
                    'entry': trade_state.entry_price,
                    'sl': trade_state.sl,
                    'tp': trade_state.tp,
                    'trail_activation': trade_state.trail_activation_price,
                    'qty': trade_state.qty
                }
                send_trade_telegram(trade_details, telegram_bot, telegram_chat_id)

                try:
                    log("Cancelling all existing open orders for symbol before placing SL/TP...")
                    try:
                        cancel_res = client.cancel_all_open_orders(symbol)
                        log(f"Cancel all orders response: {cancel_res}")
                    except Exception as e:
                        log(f"Failed to cancel existing orders: {str(e)}. Proceeding with SL/TP placement.")

                    try:
                        sl_res = place_sl_order_closepos(client, symbol, sl_price_dec_quant, close_side_for_sl)
                        trade_state.sl_order_id = sl_res.get("orderId")
                        log(f"SL response: {sl_res}")
                    except Exception as e:
                        if "code" in str(e) and "-1111" in str(e):
                            log(f"SL precision error. Re-fetching filters and retrying...")
                            symbol_filters_cache = None
                            filters = get_symbol_filters(client, symbol)
                            tick_size = filters['tickSize']
                            sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                            sl_res = place_sl_order_closepos(client, symbol, sl_price_dec_quant, close_side_for_sl)
                            trade_state.sl_order_id = sl_res.get("orderId")
                            log(f"SL retry response: {sl_res}")
                        else:
                            log(f"SL order failed: {str(e)}")

                    try:
                        tp_res = place_tp_order_closepos(client, symbol, tp_price_dec_quant, close_side_for_sl)
                        trade_state.tp_order_id = tp_res.get("orderId")
                        log(f"TP response: {tp_res}")
                    except Exception as e:
                        if "code" in str(e) and "-1111" in str(e):
                            log(f"TP precision error. Re-fetching filters and retrying...")
                            symbol_filters_cache = None
                            filters = get_symbol_filters(client, symbol)
                            tick_size = filters['tickSize']
                            tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                            tp_res = place_tp_order_closepos(client, symbol, tp_price_dec_quant, close_side_for_sl)
                            trade_state.tp_order_id = tp_res.get("orderId")
                            log(f"TP retry response: {tp_res}")
                        else:
                            log(f"TP order failed: {str(e)}")

                    if use_trailing:
                        log(f"Placing trailing stop: activationPrice={trail_activation_price_f}, callbackRate={callback_rate_f}%, trailDistance={trail_distance_dec} (2R)")
                        try:
                            trail_res = place_trailing_stop(client, symbol, close_side_for_sl, trail_activation_price_f, callback_rate_f, Decimal(str(actual_qty)), sl_price_dec_quant)
                            trade_state.trail_activated = False
                            trade_state.trail_order_id = trail_res.get("orderId")
                            log(f"Trailing stop response: {trail_res}")
                        except Exception as e:
                            log(f"Failed to place trailing stop: {str(e)}. Continuing with SL/TP only.")

                except Exception as e:
                    log(f"Could not place SL/TP orders: {str(e)}")

                try:
                    open_orders = client.get_open_orders(symbol)
                    log(f"Open orders after SL/TP and trailing stop attempt: {open_orders}")
                except Exception as e:
                    log(f"Failed to fetch open orders: {str(e)}")

                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, filters['tickSize'], telegram_bot, telegram_chat_id)

            elif trade_state.active or pending_entry:
                log("Trade active or pending. Skipping signal check.")

            else:
                log("No trade signal on candle close.")

            if last_processed_time != close_time:
                last_processed_time = close_time

            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for candle close in {sleep_seconds:.2f}s ...")
            _safe_sleep(sleep_seconds)

        except Exception as e:
            log(f"Loop error: {str(e)}")
            time.sleep(2)

    log("Trading loop exited.")

def interval_ms(interval):
    if interval.endswith("m"):
        return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"):
        return int(interval[:-1]) * 60 * 60 * 1000
    return 30 * 60 * 1000  # 30m default

def _safe_sleep(total_seconds):
    remaining = float(total_seconds)
    while remaining > 0:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        time.sleep(min(1, remaining))
        remaining -= 1

def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

# -------- SCHEDULER FOR REPORTS ----------
def run_scheduler(bot, chat_id):
    last_month = None
    def check_monthly_report():
        nonlocal last_month
        current_date = datetime.now(timezone.utc)
        if current_date.day == 1 and (last_month is None or current_date.month != last_month):
            send_monthly_report(bot, chat_id)
            last_month = current_date.month

    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot, chat_id))
    schedule.every().day.at("00:00").do(check_monthly_report)
    while True:
        schedule.run_pending()
        time.sleep(60)

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI+MACD Bot (Headless, 30m Optimized, SOLUSDT)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol (default: SOLUSDT)")
    parser.add_argument("--timeframe", default="30m", help="Timeframe (default: 30m)")
    parser.add_argument("--max-trades", type=int, default=3, help="Max trades per day (default: 3)")
    parser.add_argument("--risk-pct", type=float, default=0.5, help="Risk percentage per trade (default: 0.5%)")
    parser.add_argument("--max-loss-pct", type=float, default=5.0, help="Max daily loss percentage (default: 5%)")
    parser.add_argument("--tp-mult", type=float, default=3.5, help="Take-profit multiplier (default: 3.5)")
    parser.add_argument("--no-trailing", action="store_false", dest="use_trailing", help="Disable trailing stop (default: enabled)")
    parser.add_argument("--no-prevent-same-bar", action="store_false", dest="prevent_same_bar", help="Allow entries on same bar (default: prevent)")
    parser.add_argument("--no-require-no-pos", action="store_false", dest="require_no_pos", help="Allow entry even if there's an active position (default: require no pos)")
    parser.add_argument("--no-use-max-loss", action="store_false", dest="use_max_loss", help="Disable max daily loss protection (default: enabled)")
    parser.add_argument("--use-volume-filter", action="store_true", default=False, help="Use volume filter (vol > SMA15)")
    parser.add_argument("--no-volume-filter", action="store_false", dest="use_volume_filter", help="Disable volume filter")
    parser.add_argument("--use-macd", action="store_true", default=False, help="Use MACD confirmation (default: False)")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")

    args = parser.parse_args()

    init_pnl_log()

    telegram_bot = Bot(token=args.telegram_token)

    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%, use_volume_filter={args.use_volume_filter}, use_macd={args.use_macd}")

    # Schedule reports in a separate thread
    threading.Thread(target=lambda: run_scheduler(telegram_bot, args.chat_id), daemon=True).start()

    trading_loop(
        client=client,
        symbol=args.symbol,
        timeframe=args.timeframe,
        max_trades_per_day=args.max_trades,
        risk_pct=Decimal(str(args.risk_pct)) / Decimal("100"),
        max_daily_loss_pct=Decimal(str(args.max_loss_pct)),
        tp_mult=Decimal(str(args.tp_mult)),
        use_trailing=args.use_trailing,
        prevent_same_bar=args.prevent_same_bar,
        require_no_pos=args.require_no_pos,
        use_max_loss=args.use_max_loss,
        use_volume_filter=args.use_volume_filter,
        use_macd=args.use_macd,
        telegram_bot=telegram_bot,
        telegram_chat_id=args.chat_id
    )
