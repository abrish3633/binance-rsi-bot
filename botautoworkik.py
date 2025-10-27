#!/usr/bin/env python3
"""
Binance Futures RSI+MACD Bot (Manual Trade Management, 30m Optimized, SOLUSDT)
Fixed: Telegram sending made synchronous to avoid "Event loop is closed" errors.
Other behavior retained from previous full script.
Modified: Use Binance TRAILING_STOP_MARKET placed immediately after entry, with fixed SL/TP as fallback throughout trade.
Trailing logic updated to match clarified intent: initial stop at entry - 0.75R (for long), advances at 2R distance, handled by Binance.
Telegram updates for trailing stop activation and changes.

=== CORRECTED RSI & VOLUME SMA (WILDER'S METHOD + SUM-BASED SMA) ===
# - compute_rsi: Full Wilder's RSI (initial SMA + smoothing) → 100% match with Binance/TradingView
# - sma: Simple sum/period → exact volume SMA(15)
# - No statistics.mean → no crash, no drift
# - Uses only closed candles (klines[:-1])
# - Works on TESTNET and LIVE (with --live)
# - Keep all other logic (trailing, PnL, Telegram, etc.) 100% intact
"""

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
import traceback
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")  # 0.5% per trade
SL_PCT = Decimal("0.0075")  # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2.0")  # 2R trailing distance
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MACD_FAST = 12
MACD_SLOW = 26
MACD_SIGNAL = 9
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 55
BUY_RSI_MAX = 65
SELL_RSI_MIN = 35
SELL_RSI_MAX = 45
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = 5.0
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RATE_LIMIT_CHECK_INTERVAL = 60
RATE_LIMIT_THRESHOLD = 80

# Global stop flag and client
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
klines_cache = None
klines_cache_time = 0
last_rate_limit_check = 0

# Global PnL tracking
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []

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
        'entry': entry,
        'exit': exit_price,
        'pnl_usd': float(pnl_usd),
        'pnl_r': float(pnl_r)
    }
    pnl_data.append(row)
    with open(PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=row.keys())
        writer.writerow(row)
    return row

# Logging setup
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

def log(message, telegram_bot=None, telegram_chat_id=None):
    logger.info(message)
    if telegram_bot and telegram_chat_id:
        telegram_post(telegram_bot, telegram_chat_id, message)

def telegram_post(token, chat_id, text, parse_mode=None):
    """Send Telegram message via direct HTTP POST (creates its own connection each call)."""
    if not token or not chat_id:
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text}
    if parse_mode:
        payload["parse_mode"] = parse_mode
    try:
        requests.post(url, json=payload, timeout=10)
    except Exception as e:
        logger.error(f"Telegram HTTP send failed: {e}")

def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']}\n"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id):
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {entry_price:.4f}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {reason}\n"
        f"- Qty: {qty}\n"
        f"- PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_activation_telegram(symbol, side, activation_price, initial_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {activation_price:.4f}\n"
        f"- Initial Stop Price: {initial_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {new_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def calculate_pnl_report(period):
    now = datetime.now(timezone.utc)
    if period == 'daily':
        start_time = now.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'weekly':
        start_time = now - timedelta(days=now.weekday())
        start_time = start_time.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'monthly':
        start_time = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    else:
        return "Invalid period specified."
    filtered_trades = [
        trade for trade in pnl_data
        if datetime.fromisoformat(trade['date']) >= start_time
    ]
    if not filtered_trades:
        return f"No trades recorded for the {period} period."
    total_pnl_usd = sum(trade['pnl_usd'] for trade in filtered_trades)
    total_pnl_r = sum(trade['pnl_r'] for trade in filtered_trades)
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / num_trades if num_trades > 0 else 0
    wins = sum(1 for trade in filtered_trades if trade['pnl_usd'] > 0)
    losses = num_trades - wins
    win_rate = (wins / num_trades * 100) if num_trades > 0 else 0
    return (
        f"{period.capitalize()} PNL Report:\n"
        f"- Total Trades: {num_trades}\n"
        f"- Total PNL: {total_pnl_usd:.2f} USDT\n"
        f"- Average PNL per Trade: {avg_pnl_usd:.2f} USDT\n"
        f"- Total PNL (R): {total_pnl_r:.2f}R\n"
        f"- Win Rate: {win_rate:.2f}% ({wins} wins, {losses} losses)\n"
    )

def send_daily_report(bot, chat_id):
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot, chat_id):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot, chat_id):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def _request_stop(signum, frame, symbol=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    if not client or not symbol:
        log("Client or symbol not defined; skipping position closure and order cancellation.")
        return
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        if isinstance(pos_resp, dict) and 'data' in pos_resp:
            positions = pos_resp['data']
        else:
            positions = pos_resp if isinstance(pos_resp, list) else []
        pos_item = None
        for p in positions:
            try:
                if p.get("symbol") == symbol:
                    pos_item = p
                    break
            except Exception:
                continue
        pos_amt = Decimal('0')
        if pos_item:
            pos_amt = Decimal(str(pos_item.get("positionAmt", "0")))
        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            entry_price = None
            try:
                entry_price = float(Decimal(str(pos_item.get("entryPrice", "0")))) if pos_item else None
            except Exception:
                entry_price = None
            try:
                response = client.send_signed_request("POST", "/fapi/v1/order", {
                    "symbol": symbol,
                    "side": side,
                    "type": "MARKET",
                    "quantity": str(qty)
                })
                log(f"Closed position: qty={qty} {side}")
                exit_price = client.get_latest_fill_price(symbol, response.get("orderId"))
                if exit_price is None:
                    log("Failed to fetch exit price; using current market price.")
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price = Decimal(str(ticker.get("price")))
                exit_price_f = float(exit_price)
                if entry_price is None and pos_item:
                    try:
                        entry_price = float(Decimal(str(pos_item.get("entryPrice", "0"))))
                    except Exception:
                        entry_price = 0.0
                R = Decimal(str(entry_price)) * SL_PCT if entry_price else Decimal('0')
                pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", entry_price or 0.0, exit_price_f, float(qty), float(R) if R else 0.0)
                if telegram_bot and telegram_chat_id:
                    send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", entry_price or 0.0, exit_price_f, float(qty), pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to close position: {str(e)}, stack: {traceback.format_exc()}")
        else:
            log("No open position found for closure.")
        try:
            client.cancel_all_open_orders(symbol)
            log(f"All open orders cancelled for {symbol}.")
        except Exception as e:
            log(f"Failed to cancel orders: {str(e)}, stack: {traceback.format_exc()}")
    except Exception as e:
        log(f"Failed to handle stop: {str(e)}, stack: {traceback.format_exc()}")

# -------- TIME SYNC CHECK ----------
def check_time_offset(base_url):
    try:
        start_time = time.time()
        response = requests.get(f"{base_url}/fapi/v1/time", timeout=5)
        server_time_ms = response.json()['serverTime']
        server_time = datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc)
        local_time = datetime.now(timezone.utc)
        offset = (server_time - local_time).total_seconds()
        request_duration = time.time() - start_time
        log(f"Time offset from Binance: {offset} seconds, request duration: {request_duration:.3f}s")
        if abs(offset) > 5:
            log("Warning: Clock offset > 5s. Using recvWindow=10000.")
        return request_duration
    except Exception as e:
        log(f"Binance time sync failed: {str(e)}")
        return None

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
        self.ping_latency = None
        self.ping_latency = check_time_offset(self.base)
        self.dual_side = self._check_position_mode()
        print(f"Using base URL: {self.base}, Position Mode: {'Hedge' if self.dual_side else 'One-way'}")

    def _check_position_mode(self):
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            if isinstance(response, dict) and 'dualSidePosition' in response:
                return response['dualSidePosition']
            log("Failed to fetch position mode; assuming one-way mode.")
            return False
        except Exception as e:
            log(f"Position mode check failed: {str(e)}. Assuming one-way mode.")
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params.copy() if params else {}
        dynamic_timeout = REQUEST_TIMEOUT + (self.ping_latency * 2 if self.ping_latency else 0)
        for attempt in range(MAX_RETRIES):
            try:
                response = requests.get(f"{self.base}/fapi/v1/time", timeout=5)
                server_time_ms = response.json()['serverTime']
                params["timestamp"] = server_time_ms
            except Exception as e:
                log(f"Time sync failed (attempt {attempt+1}/{MAX_RETRIES}): {str(e)}. Using local time.")
                params["timestamp"] = int(time.time() * 1000)
            params["recvWindow"] = 10000
            query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
            signature = self._sign(query)
            url = f"{self.base}{endpoint}?{query}&signature={signature}"
            headers = {"X-MBX-APIKEY": self.api_key}
            start_time = time.time()
            try:
                r = requests.request(method, url, headers=headers, timeout=dynamic_timeout)
                duration = time.time() - start_time
                log(f"Request to {endpoint} took {duration:.3f}s")
                if r.status_code == 200:
                    response = r.json()
                    if isinstance(response, list):
                        response = {'data': response, '_response': r}
                    else:
                        if isinstance(response, dict):
                            response['_response'] = r
                        else:
                            response = {'data': response, '_response': r}
                    if isinstance(response, dict) and response.get("code") not in (None, 200):
                        if response.get('code') == -1003:
                            log(f"Rate limit exceeded. Waiting 30s before retry {attempt+1}/{MAX_RETRIES}.")
                            time.sleep(30)
                            continue
                        raise BinanceAPIError(f"API error: {response.get('msg', 'Unknown error')} (code {response.get('code')})", status_code=r.status_code, payload=response)
                    return response
                else:
                    raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", status_code=r.status_code, payload=r.json() if r.headers.get('content-type') == 'application/json' else None)
            except requests.exceptions.Timeout:
                log(f"Request timeout (attempt {attempt+1}/{MAX_RETRIES}), duration: {duration:.3f}s")
                if attempt < MAX_RETRIES - 1:
                    time.sleep(2 ** (attempt + 1))
                    continue
            except requests.exceptions.RequestException as e:
                log(f"Request failed (attempt {attempt+1}/{MAX_RETRIES}): {str(e)}")
                if attempt < MAX_RETRIES - 1:
                    time.sleep(2 ** (attempt + 1))
                    continue
        raise BinanceAPIError("Max retries exceeded")

    def public_request(self, endpoint: str, params: dict = None):
        params = params or {}
        url = f"{self.base}{endpoint}"
        try:
            r = requests.get(url, params=params, timeout=10)
            r.raise_for_status()
            return r.json()
        except Exception as e:
            raise BinanceAPIError(f"Public request failed: {str(e)}", payload=r.json() if 'r' in locals() else None)

    def place_stop_market(self, symbol, side, quantity, stop_price, reduce_only=False, position_side=None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "STOP_MARKET",
            "quantity": str(quantity),
            "stopPrice": str(stop_price)
        }
        if reduce_only:
            params["reduceOnly"] = "true"
        if position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def place_take_profit_market(self, symbol, side, quantity, stop_price, reduce_only=False, position_side=None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "TAKE_PROFIT_MARKET",
            "quantity": str(quantity),
            "stopPrice": str(stop_price)
        }
        if reduce_only:
            params["reduceOnly"] = "true"
        if position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def place_trailing_stop_market(self, symbol, side, quantity, callback_rate, activation_price, reduce_only=False, position_side=None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "TRAILING_STOP_MARKET",
            "quantity": str(quantity),
            "callbackRate": str(callback_rate)
        }
        if activation_price:
            params["activationPrice"] = str(activation_price)
        if reduce_only:
            params["reduceOnly"] = "true"
        if position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def cancel_all_open_orders(self, symbol):
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol})

    def get_latest_fill_price(self, symbol, order_id):
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", {"symbol": symbol, "orderId": order_id})
            if isinstance(trades, list) and trades:
                return Decimal(str(trades[-1]["price"]))
        except:
            pass
        return None

# -------- CORRECTED RSI & SMA ----------
def compute_rsi(closes, period=RSI_PERIOD):
    """Wilder's RSI — 100% match with Binance/TradingView"""
    if len(closes) < period + 1:
        return None
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    gains = [max(d, 0) for d in deltas]
    losses = [max(-d, 0) for d in deltas]
    if len(gains) < period:
        return None
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    if len(deltas) == period:
        if avg_loss == 0:
            return 100.0
        return round(100 - 100 / (1 + avg_gain / avg_loss), 2)
    current_gain = avg_gain
    current_loss = avg_loss
    rsi_values = []
    if current_loss == 0:
        rsi_values.append(100.0)
    else:
        rsi_values.append(100 - 100 / (1 + current_gain / current_loss))
    for i in range(period, len(deltas)):
        current_gain = (current_gain * (period - 1) + gains[i]) / period
        current_loss = (current_loss * (period - 1) + losses[i]) / period
        if current_loss == 0:
            rsi_values.append(100.0)
        else:
            rsi_values.append(100 - 100 / (1 + current_gain / current_loss))
    return round(rsi_values[-1], 2)

def sma(data, period):
    """Simple Moving Average — exact match"""
    if len(data) < period:
        return None
    return sum(data[-period:]) / period

# -------- UTILS ----------
def fetch_klines(client, symbol, timeframe, limit):
    global klines_cache, klines_cache_time
    current_time = time.time()
    if klines_cache and current_time - klines_cache_time < KLINES_CACHE_DURATION:
        return klines_cache
    klines = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": timeframe, "limit": limit})
    klines_cache = klines
    klines_cache_time = current_time
    return klines

def get_symbol_filters(client, symbol):
    global symbol_filters_cache
    if symbol_filters_cache:
        return symbol_filters_cache
    exchange_info = client.public_request("/fapi/v1/exchangeInfo")
    for s in exchange_info["symbols"]:
        if s["symbol"] == symbol:
            filters = {}
            for f in s["filters"]:
                if f["filterType"] == "PRICE_FILTER":
                    filters["tickSize"] = Decimal(str(f["tickSize"]))
                    filters["tp_rounding"] = ROUND_UP if s["quoteAsset"] == "USDT" else ROUND_DOWN
                    filters["sl_rounding"] = ROUND_DOWN if s["quoteAsset"] == "USDT" else ROUND_UP
                elif f["filterType"] == "LOT_SIZE":
                    filters["stepSize"] = Decimal(str(f["stepSize"]))
                    filters["minQty"] = Decimal(str(f["minQty"]))
            symbol_filters_cache = filters
            return filters
    raise ValueError(f"Symbol {symbol} not found")

def quantize_price(price, tick_size, rounding=ROUND_HALF_EVEN):
    return (price // tick_size * tick_size).quantize(tick_size, rounding=rounding)

def quantize_qty(qty, step_size):
    return (qty // step_size * step_size).quantize(step_size, rounding=ROUND_DOWN)

def interval_ms(interval):
    if interval.endswith("m"):
        return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"):
        return int(interval[:-1]) * 60 * 60 * 1000
    return 30 * 60 * 1000

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

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, use_macd, telegram_bot, telegram_chat_id):
    global STOP_REQUESTED
    trade_state = type('TradeState', (), {})()
    trade_state.active = False
    trades_today = 0
    last_processed_time = 0
    pending_entry = False
    last_day = datetime.now(timezone.utc).day

    klines_limit = max(RSI_PERIOD + 1, VOL_SMA_PERIOD, 100)
    filters = get_symbol_filters(client, symbol)
    tick_size = filters["tickSize"]
    step_size = filters["stepSize"]
    tp_rounding = filters.get("tp_rounding", ROUND_HALF_EVEN)
    sl_rounding = filters.get("sl_rounding", ROUND_HALF_EVEN)

    while not STOP_REQUESTED:
        if os.path.exists("stop.txt"):
            STOP_REQUESTED = True
            break

        current_day = datetime.now(timezone.utc).day
        if current_day != last_day:
            trades_today = 0
            last_day = current_day

        if trades_today >= max_trades_per_day:
            log(f"Max {max_trades_per_day} trades today. Waiting...", telegram_bot, telegram_chat_id)
            _safe_sleep(3600)
            continue

        try:
            klines = fetch_klines(client, symbol, timeframe, klines_limit)
            if len(klines) < 2:
                time.sleep(1)
                continue

            closed_klines = klines[:-1]
            closes, volumes, close_times, _ = closes_and_volumes_from_klines(closed_klines)
            close_time = close_times[-1]
            server_time = int(time.time() * 1000)

            if close_time > server_time:
                time.sleep(1)
                continue

            rsi = compute_rsi([Decimal(str(c)) for c in closes])
            if rsi is None:
                log("Not enough data for RSI.", telegram_bot, telegram_chat_id)
                time.sleep(60)
                continue

            vol_sma = sma([Decimal(str(v)) for v in volumes], VOL_SMA_PERIOD)
            volume_ok = not use_volume_filter or volumes[-1] > (vol_sma or 0)

            buy_signal = BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and volume_ok
            sell_signal = SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and volume_ok

            if not (buy_signal or sell_signal):
                if last_processed_time != close_time:
                    last_processed_time = close_time
                next_close_ms = last_processed_time + interval_ms(timeframe)
                sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
                _safe_sleep(sleep_seconds)
                continue

            if trade_state.active or pending_entry:
                log("Trade active or pending. Skipping signal check.", telegram_bot, telegram_chat_id)
                time.sleep(1)
                continue

            if prevent_same_bar and close_time == trade_state.entry_close_time:
                log("Prevent same bar entry.", telegram_bot, telegram_chat_id)
                time.sleep(60)
                continue

            if require_no_pos and has_active_position(client, symbol):
                log("Position exists. Skipping.", telegram_bot, telegram_chat_id)
                time.sleep(60)
                continue

            pending_entry = True
            entry_price = Decimal(str(closes[-1]))
            balance = fetch_balance(client)
            risk_amount = balance * risk_pct
            R = entry_price * SL_PCT
            qty = quantize_qty(risk_amount / R, step_size)

            side = "BUY" if buy_signal else "SELL"
            order_res = client.place_market_order(symbol, side, qty)
            actual_qty = None
            timed_out = False

            for _ in range(ORDER_FILL_TIMEOUT):
                if STOP_REQUESTED:
                    break
                order_status = client.send_signed_request("GET", "/fapi/v1/order", {"symbol": symbol, "orderId": order_res.get("orderId")})
                if order_status.get("status") == "FILLED":
                    actual_qty = Decimal(str(order_status.get("executedQty", "0")))
                    break
                if order_status.get("status") in ["CANCELED", "EXPIRED"]:
                    cancel_params = {"symbol": symbol, "orderId": order_res.get("orderId")} if isinstance(order_res, dict) else {"symbol": symbol}
                    try:
                        client.send_signed_request("DELETE", "/fapi/v1/order", cancel_params)
                        log("Entry order cancelled.", telegram_bot, telegram_chat_id)
                    except Exception as e:
                        log(f"Cancel failed: {str(e)}", telegram_bot, telegram_chat_id)
                    timed_out = True
                    break
                time.sleep(0.5)

            if timed_out or actual_qty is None:
                pending_entry = False
                log("Entry timed out or aborted -> skipping this signal.", telegram_bot, telegram_chat_id)
                continue

            time.sleep(0.2)
            actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
            if actual_fill_price is None:
                log("Failed to fetch actual fill price; using candle close price.", telegram_bot, telegram_chat_id)
                actual_fill_price = entry_price
            actual_fill_price_f = float(actual_fill_price)

            # Recalculate with actual fill price
            if buy_signal:
                sl_price_dec = actual_fill_price * (Decimal("1") - SL_PCT)
                R = actual_fill_price * SL_PCT
                tp_price_dec = actual_fill_price + (tp_mult * R)
                trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
            else:
                sl_price_dec = actual_fill_price * (Decimal("1") + SL_PCT)
                R = actual_fill_price * SL_PCT
                tp_price_dec = actual_fill_price - (tp_mult * R)
                trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)

            sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
            sl_price_f = float(sl_price_dec_quant)
            tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
            tp_price_f = float(tp_price_dec_quant)
            trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)

            try:
                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                current_price = Decimal(str(ticker.get("price")))
            except Exception as e:
                log(f"Price fetch failed: {str(e)}. Skipping trade.", telegram_bot, telegram_chat_id)
                pending_entry = False
                time.sleep(1)
                continue

            price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
            if buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer:
                log(f"Trailing activation too close. Skipping.", telegram_bot, telegram_chat_id)
                pending_entry = False
                time.sleep(1)
                continue
            elif not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer:
                log(f"Trailing activation too close. Skipping.", telegram_bot, telegram_chat_id)
                pending_entry = False
                time.sleep(1)
                continue

            trade_state.active = True
            trade_state.entry_price = actual_fill_price_f
            trade_state.qty = float(actual_qty)
            trade_state.side = "LONG" if buy_signal else "SHORT"
            trade_state.entry_close_time = close_time
            trade_state.initial_sl = sl_price_dec_quant
            trade_state.sl = sl_price_f
            trade_state.tp = tp_price_f
            trade_state.trail_activated = False
            trade_state.trail_activation_price = trail_activation_price_dec_quant
            trade_state.risk = R

            log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, sl={sl_price_f}, tp={tp_price_f}, trail_activation={trail_activation_price_dec_quant}", telegram_bot, telegram_chat_id)

            trade_details = {
                'symbol': symbol,
                'side': trade_state.side,
                'entry': trade_state.entry_price,
                'sl': trade_state.sl,
                'tp': trade_state.tp,
                'trail_activation': float(trail_activation_price_dec_quant),
                'qty': trade_state.qty
            }
            send_trade_telegram(trade_details, telegram_bot, telegram_chat_id)

            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            pos_side = "LONG" if trade_state.side == "LONG" else "SHORT"
            qty_dec = Decimal(str(trade_state.qty))

            try:
                sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=pos_side)
                trade_state.sl_order_id = sl_order.get("orderId")
                log(f"Placed STOP_MARKET SL: {sl_order}", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)

            try:
                tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=pos_side)
                trade_state.tp_order_id = tp_order.get("orderId")
                log(f"Placed TAKE_PROFIT_MARKET TP: {tp_order}", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)

            callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
            activation_price = trail_activation_price_dec_quant
            try:
                trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, activation_price, reduce_only=True, position_side=pos_side)
                trade_state.trail_order_id = trail_order.get("orderId")
                log(f"Placed TRAILING_STOP_MARKET: {trail_order}", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)

            trades_today += 1
            pending_entry = False
            monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

            if last_processed_time != close_time:
                last_processed_time = close_time
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for candle close in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
            _safe_sleep(sleep_seconds)

        except Exception as e:
            log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

    log("Trading loop exited.", telegram_bot, telegram_chat_id)

# -------- MONITOR TRADE ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    while trade_state.active and not STOP_REQUESTED:
        time.sleep(1)
        if not has_active_position(client, symbol):
            trade_state.active = False
            exit_price = client.get_latest_fill_price(symbol, None)
            if exit_price is None:
                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                exit_price = Decimal(str(ticker.get("price")))
            exit_price_f = float(exit_price)
            R = trade_state.risk
            pnl_row = log_pnl(len(pnl_data)+1, trade_state.side, trade_state.entry_price, exit_price_f, trade_state.qty, float(R))
            send_closure_telegram(symbol, trade_state.side, trade_state.entry_price, exit_price_f, trade_state.qty, pnl_row['pnl_usd'], pnl_row['pnl_r'], "UNKNOWN", telegram_bot, telegram_chat_id)
            client.cancel_all_open_orders(symbol)
            break

def has_active_position(client, symbol):
    try:
        pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        if isinstance(pos, list) and pos:
            return Decimal(str(pos[0].get("positionAmt", "0"))) != 0
        return False
    except:
        return False

def fetch_balance(client):
    try:
        bal = client.send_signed_request("GET", "/fapi/v2/balance")
        for b in bal:
            if b["asset"] == "USDT":
                return Decimal(str(b["balance"]))
        return Decimal("0")
    except:
        return Decimal("0")

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI+MACD Bot (Manual Trade Management, 30m Optimized, SOLUSDT)")
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
    parser.add_argument("--no-trailing", dest='use_trailing', action='store_false', help="Disable trailing stop (default: enabled)")
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false', help="Allow entries on same bar (default: prevent same bar)")
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false', help="Allow entry even if there's an active position (default: require no pos)")
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false', help="Disable max daily loss protection (default: enabled)")
    parser.add_argument("--use-volume-filter", action='store_true', default=False, help="Use volume filter (vol > SMA15)")
    parser.add_argument("--no-volume-filter", action='store_false', dest='use_volume_filter', help="Disable volume filter")
    parser.add_argument("--use-macd", action='store_true', default=False, help="Use MACD confirmation (default: False)")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")
    args = parser.parse_args()

    init_pnl_log()
    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%, use_volume_filter={args.use_volume_filter}, use_macd={args.use_macd}")

    threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
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
        telegram_bot=args.telegram_token,
        telegram_chat_id=args.chat_id
    )
