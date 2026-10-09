'use strict';
throw new Error('Network-enabled legacy program is quarantined. Use src/demo.js for offline research.');
"use strict";
const FAIR_PRICE_THRESHOLD_LONG = 0.125; //  threshold for LONG positions
const FAIR_PRICE_THRESHOLD_SHORT = 0.075; // threshold for SHORT positions
const MAX_OPEN_POSITIONS = 5; // Maximum number of open positions allowed at the same time
const TP_LIMIT_1_PCT = 0.02; 
const TP_LIMIT_2_PCT = 0.03; 
const TP_LIMIT_3_PCT = 0.04; 
// Auto-install dependencies if missing
const fs = require('fs');
const path = require('path');

const crypto = require('crypto');
const axios = require('axios');
const WebSocket = require('ws');
const https = require('https');
const TelegramBot = require('node-telegram-bot-api');

// Import API keys from external file
const {
  MEXC_WEB_TOKEN,
  MEXC_SPOT_API_KEY,
  MEXC_SPOT_API_SECRET
} = require('../src/config');

// Balance is fetched via WEB token (MEXC_KEY) - API key/secret method always returns 401

// Configuration
const MEXC_KEY = MEXC_WEB_TOKEN;
const USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36";
// Create a new log file per run so logs don't grow unbounded.
function makeRunLogPath(basePath, runTag) {
  const p = basePath || path.join(__dirname, 'mexc_fairprice.log');
  const parsed = path.parse(p);
  const ext = parsed.ext || '.log';
  return path.join(parsed.dir, `${parsed.name}_${runTag}${ext}`);
}

const RUN_TAG = new Date().toISOString().replace(/[:.]/g, '-'); // safe for Windows filenames
const LOG_FILE_BASE = path.join(__dirname, 'mexc_fair_GMGN_spot.log');
const LOG_FILE = makeRunLogPath(LOG_FILE_BASE, RUN_TAG);
// Environment variables hold credentials; strategy parameters remain constants.
const ORDERBOOK_DEPTH = 5; // Depth limit for sub.depth.full
const MAX_SLIPPAGE_BPS = 50; // target slippage limit for sizing
const OB_SCAN_INTERVAL_MS = 15000; // how often to scan orderbooks for slippage sizing (WebSocket depth first)
const OB_SCAN_DEPTH_LEVELS = ORDERBOOK_DEPTH; // depth levels to use for slippage calc (WS)
const OB_REST_SCAN_INTERVAL_MS = 180000; // how often to refresh deep OB via REST for missing symbols
const OB_REST_DEPTH = 50; // depth levels for REST fallback
const OB_REST_PAUSE_MS = 300; // pause between REST requests to avoid rate limits
const SLIPPAGE_TEST_NOTIONAL = 50; // target notional to test if WS depth is sufficient; else fallback to REST
const ENABLE_LONG = true; // Enable/disable LONG trading
const ENABLE_SHORT = true; // Enable/disable SHORT trading
const DEFAULT_MIN_MARGIN_USDT = 0.1; // Default minimum margin fallback (if not found in API)
const MAX_LEVERAGE = 500; // Maximum leverage to try (MEXC supports up to 500x)
const STALE_ORDERBOOK_MS = 5000; // Consider OB stale after this
const STALE_TICKER_MS = 5000; // Consider ticker stale after this
const MAX_ORDERBOOK_SOCKETS = 300; // Cap per-symbol OB WS to limit load
const INFLIGHT_TTL_MS = 120000; // Drop in-flight opens after this to avoid deadlocks
const LAST_CLOSE_DIRECTION_COOLDOWN_MS = 10 * 1000; // 10 seconds cooldown before re-entering same direction
const PRICE_TREND_WINDOW_MS = 10000; // evaluate last 10s of price ticks for re-entry
const PRICE_HISTORY_RETENTION_MS = 15000; // keep a small buffer of price history

// Stop Loss constants (from spread.js)
const GLOBAL_STOP_LOSS_PERCENT = 50; // stop-loss for SHORT positions
const LONG_STOP_LOSS_PERCENT = 5; // stop-loss for LONG positions
const STOPLOSS_BANLIST_THRESHOLD_FACTOR = 0.9; // % of SL move that counts toward banlist streak
const STOPLOSS_HISTORY_SIZE = 10; // lookback window for stop-loss hits (last 10 deals)
const STOPLOSS_HISTORY_REQUIRED_SL = 2; // banlist if >=2 SL within window
const LONG_BANLIST_NET_LOSS_THRESHOLD = 10; // banlist if net loss >= 10% for longs

// Position management configuration
const SPREAD_PARTIAL_CLOSE_THRESHOLD = 0.0125; // 1.25% spread -> take partial profits
const SPREAD_FINAL_CLOSE_THRESHOLD = 0.01; // 1% spread -> close remainder
const PARTIAL_CLOSE_RATIO = 0.5; // Close 50% of volume on partial event
const MAX_POSITION_DURATION_MS = 45 * 60 * 1000; // Kill switch after 45 minutes
const MAX_DRAWDOWN_PERCENT = 0.03; // Close if unrealized loss exceeds 3%
const MANUAL_HOLD_8819_MS = 60 * 1000; // Hold symbol for 60s after 8819 to avoid repeated attempts
const CLOSE_RETRY_INTERVAL_MS = 5000; // Retry reduce-only close after 5 seconds
const MAX_CLOSE_RETRIES = 3; // Give up after N retries

// ---------------------- GMGN spread strategy (from mexc_tp.js) ----------------------
const ENABLE_GMGN_SPREAD_TRADING = false;
const GMGN_FIXED_MARGIN_PERCENT = 5; // Fixed: each GMGN trade uses 5% of deposit

// GMGN WS connection pacing (helps mitigate 429)
const GMGN_WS_CONNECT_DELAY_MIN_MS = 3000;
const GMGN_WS_CONNECT_DELAY_MAX_MS = 5000;

// GMGN spread trading behavior/filters
const GMGN_MIN_VOLUME_FILTER = 1000; // gmgn volume threshold used in mexc_tp.js
const GMGN_ADVERSE_SPREAD_THRESHOLD = 1.0 / 100; // 1% adverse spread => emergency close
const GMGN_LAST_CLOSE_DIRECTION_COOLDOWN_MS = 60 * 1000; // mexc_tp.js uses 60s cooldown
const GMGN_DEFAULT_MARGIN_PERCENT = 5;
const GMGN_DEFAULT_LEVERAGE = 5;

// FAIR strategy risk settings
const FAIR_FIXED_MARGIN_PERCENT = 25; // Fixed: each FAIR trade uses 25% of deposit

// Optional volume filter (parity with mexc_tp.js)
const ENABLE_GMGN_VOLUME_FILTER = true;
const MIN_DAILY_VOLUME_USD = 10000;
const MAX_VOLUME_FETCH_ATTEMPTS = 2;
const VOLUME_RETRY_BASE_DELAY_MS = 1000;
const VOLUME_RETRY_MAX_DELAY_MS = 10000;

// Optional deposit/withdraw filter (Spot API, parity with mexc_tp.js)
const ENABLE_DEPOSIT_WITHDRAW_CHECK = true;
// API keys are now imported from api_keys.js
const DEPOSIT_WITHDRAW_URL = 'https://api.mexc.com/api/v3/capital/config/getall';
const MEXC_TIME_URL = 'https://api.mexc.com/api/v3/time';
const DEPOSIT_WITHDRAW_CACHE_DURATION_MS = 300000; // 5 minutes
const DEPOSIT_WITHDRAW_CHECK_INTERVAL_MS = 180000; // 3 minutes (avoids rate limits)

// TP open-threshold rules (parity with mexc_tp.js)
const DEFAULT_OPEN_THRESHOLD = 6;
const SPECIAL_OPEN_THRESHOLDS = { CYPR: 5 };
const OPEN_THRESHOLD_EXCEPTIONS = new Set([
  'PUP','PTB','MEMERUSH','DREAMSX402','WOJAKONX','JESSE','STARTUP','CHILLHOUSE',
  'MAIGA','FUNSOL','CARDS','AKE','XNAP'
]);

// TP script ticker blacklist (parity with mexc_tp.js)
const BLACKLISTED_TICKERS = new Set(['L3', 'CORL', 'PAYAI', 'ELIZAOS', 'BEAT', 'AVICI', 'CLOUD']);

// ---------------------- SPOT-FUTURES ARBITRAGE STRATEGY ----------------------
const ENABLE_SPOT_FUTURES_ARBITRAGE = false; // Отключено
const SPOT_FUTURES_OPEN_THRESHOLD = 0.085; // 8.5% - minimum spread to open arbitrage position
// Spot-futures close threshold is time-dependent:
// - if position age < SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS => use SPOT_FUTURES_CLOSE_THRESHOLD_SHORT
// - else => use SPOT_FUTURES_CLOSE_THRESHOLD_LONG
const SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS = 60 * 60 * 1000; // 1 hour
const SPOT_FUTURES_CLOSE_THRESHOLD_SHORT = 0.015; // 1.5% - close when spread converges (young positions)
const SPOT_FUTURES_CLOSE_THRESHOLD_LONG = 0.035; // 3.5% - close when spread converges (older positions)
const SPOT_FUTURES_MAX_POSITIONS = 4; // Maximum concurrent arbitrage positions
const SPOT_ARB_SKIP_LOG_COOLDOWN_MS = 30000; // throttle skip logs per symbol
const POSITION_UPDATE_FRESH_MS = 30000; // consider position WS fresh within 30s
const ACTIVE_TRADE_STALE_GRACE_MS = 15000; // allow WS to confirm close before cleanup
const ACTIVE_TRADE_STALE_MAX_AGE_MS = 15 * 60 * 1000; // fallback cleanup if no updates
// const SPOT_FUTURES_BALANCE_PERCENT = 0.10; // DEPRECATED: Now using dynamic allocation based on position index
const SPOT_FUTURES_LEVERAGE = 1; // 1x leverage for futures short (cross margin)
const SPOT_FUTURES_MARGIN_TYPE = 2; // 2 = cross margin (openType)
const SPOT_MARKET_SCAN_INTERVAL_MS = 60000; // Scan spot market data every 60 seconds
const SPOT_ORDERBOOK_DEPTH = 5; // Depth for spot orderbook (WS only)
// NOTE: MEXC spot public WS (wbs.mexc.com) often replies "Not Subscribed successfully ... Reason: Blocked!"
// so we use REST bookTicker as default data source for spot best bid/ask.
const ENABLE_SPOT_ORDERBOOK_WS = false;
const SPOT_BOOKTICKER_URL = 'https://api.mexc.com/api/v3/ticker/bookTicker';
const SPOT_BOOKTICKER_POLL_INTERVAL_MS = 2000; // 2s
const SPOT_FUTURES_MAX_DRAWDOWN_PERCENT = -1; // -100% - disable drawdown check
const SPOT_FUTURES_MAX_DURATION_MS = Infinity; // Infinity - disable timeout check

// Blacklist of symbols to ignore
let BLACKLISTED_SYMBOLS = new Set([
  'BTC_MUSDT',
  'BNBHOLDER_USDT',
  'LISA_USDT',
  'AVICI_USDT',
  '1_USDT'
]);

// Blacklist file paths
const BLACKLIST_FAIR_FILE = path.join(__dirname, 'blacklist_fair.json');
const BLACKLIST_SPREAD_FILE = path.join(__dirname, 'blacklist_spread.json');
const STOPLOSS_BLACKLIST_FILE = path.join(__dirname, 'stoploss_blacklist.json');

// Stop-loss banlist tracking
const STOPLOSS_BLACKLIST = new Set(); // dynamic banlist for repeated stop-loss hits
const stopLossHistory = {}; // normalizedSymbol -> array of recent stop-loss outcomes
const longPnLHistory = {}; // normalizedSymbol -> array of PnL percentages for LONG positions only

// Global state
let contract_details = {};
let contract_sizes = {};
const contractMaxVolOverrides = {}; // Track maxVol overrides from API errors
let contractRefreshInProgress = false;   // guard for periodic contract detail refresh
let available_balance = null;
let balanceReady = false;
let tickerData = {}; // symbol -> { markPrice, lastPrice, lastUpdate }
let orderbooks = {}; // symbol -> { buy_orders, sell_orders, best_buy, best_sell }
let orderbookUpdatersStarted = new Set(); // Track which symbols have orderbook updaters started
let processedSymbols = new Set(); // Track symbols we've already processed to avoid duplicates
// lastOrderTime reserved (no throttle in current logic)
let lastOrderTime = {};
let zeroLastPriceWarnings = {}; // Track symbols with lastPrice=0 to avoid spam
let symbolIsUSDT = {}; // Cache: symbol -> boolean (is USDT pair)
const activeTrades = new Map(); // symbol -> trade management state
const inFlightOpens = new Map(); // symbol -> { count, ts }
const lastCloseTimes = {}; // symbol -> { long, short }
const lastCloseLosses = {}; // symbol -> [{ isLong, pnl, timestamp }] - последние закрытия с убытком для GMGN
const GMGN_CONSECUTIVE_LOSS_COOLDOWN_MS = 60 * 1000; // 60 секунд кд при двух минусах подряд
const GMGN_CONSECUTIVE_LOSS_THRESHOLD_USD = 6; // Убыток > 6$ для активации кд
const GMGN_CONSECUTIVE_LOSS_BAN_COUNT = 2; // Бан при двух проигрышах подряд
const pendingTPRetries = new Map(); // symbol -> Array of { tpIndex, price, vol, isLong, leverage, openType, retryAfter, retryCount }
const positionTpOrders = {}; // positionId -> [orderId1, orderId2, ...] (for GMGN strategy)
const positionOpenPrices = {}; // positionId -> {gmgnPrice, mexcPrice, type, margin, leverage, entryTime} (for GMGN strategy timeout check)
const mexcPriceHistory = {}; // symbol -> [{ time, bestBuy, bestSell }]
const maxPositionNotional = new Map(); // symbol -> { long: notionalUSDT, short: notionalUSDT, worst: notionalUSDT, ts }
const lastRestScanTs = new Map(); // symbol -> last REST deep scan timestamp
const spotArbSkipLogTs = new Map(); // key -> last log timestamp
const gmgnSkipLogTs = new Map(); // key -> last GMGN skip log timestamp
const gmgnWsParseErrorTs = new Map(); // tokenKey -> last WS parse error log timestamp
const lastSymbolPositionUpdateTs = new Map(); // symbol -> last position WS update time
const logStream = fs.createWriteStream(LOG_FILE, { flags: 'w' });

// GMGN TP strategy state (from mexc_tp.js)
let gmgnPrices = {}; // tokenKey -> current GMGN price
let gmgnVolumes = {}; // tokenKey -> current GMGN volume
let gmgnSubscriptionCounter = 0;
const gmgnSubscribedTokens = new Set(); // track which tokens have been counted (not on reconnect)
let gmgnSubscriptions = []; // [{network, tokenContractAddress, tokenKey, mexc_name, ...}]
const gmgnTokenKeyToSubscription = {};
const gmgnSymbolToTokenKey = {};
const gmgnConfigBySymbol = new Map(); // symbol -> cfg (fast lookup)
let gmgnTokenConfigs = []; // loaded from mexc_tp.js (list of tokens + params)

// Deposit/withdraw blacklist state (Spot API)
const DEPOSIT_WITHDRAWAL_BLACKLIST = new Set(); // stores normalized tickers (no _USDT)
let depositWithdrawCache = null;
let lastDepositWithdrawCacheUpdate = 0;

// ---------------------- SPOT-FUTURES ARBITRAGE STATE ----------------------
let spotSymbols = new Set(); // Set of spot trading symbols (e.g., 'BTCUSDT')
let spotSymbolDetails = {}; // symbol -> { baseAsset, quoteAsset, minQty, maxQty, stepSize, minNotional, tickSize }
let spotOrderbooks = {}; // symbol -> { bids, asks, best_bid, best_ask, depthTs }
let spotOrderbookUpdatersStarted = new Set(); // Track started spot orderbook websockets
let spotAvailableBalance = null; // USDT balance on spot account
let spotBalanceReady = false;
const spotFuturesArbitragePositions = new Map(); // arbitrageId -> { spotSymbol, futuresSymbol, spotQty, futuresVol, spotEntryPrice, futuresEntryPrice, openSpread, openTime, status }
// Spot-futures blacklist:
// - static: manual blocks you want to enforce regardless of deposit/withdraw status
// - dynamic: auto blocks for symbols where deposit/withdraw is CLOSED
const SPOT_FUTURES_STATIC_BLACKLIST = new Set([
  'FISUSDT'
]);
const spotFuturesBlacklist = new Set(SPOT_FUTURES_STATIC_BLACKLIST); // Spot symbols blocked from arbitrage
let lastSpotMarketScanTime = 0;
let spotBookTickerPollerRunning = false;
let spotBookTickerLastUpdate = 0;
let spotWsBlocked = false; // runtime detection: WS subscription blocked by MEXC
let spotWsBlockedLogged = false;
let spotTradingDisabled = false;
let spotTradingDisabledLogged = false;
let spotFuturesOpenInFlight = false;
const spotFuturesLastAttemptTs = new Map(); // spotSymbol -> ts
const SPOT_FUTURES_OPEN_ATTEMPT_COOLDOWN_MS = 5000; // avoid spam attempts per symbol

function disableSpotTradingOnce(reason) {
  spotTradingDisabled = true;
  if (!spotTradingDisabledLogged) {
    spotTradingDisabledLogged = true;
    logError(`[SPOT] 🛑 Spot trading DISABLED: ${reason}`);
  }
}

// Trade notifications file (same as spread.js)
const TRADE_NOTIFICATIONS_FILE = path.join(__dirname, 'trade_notifications.json');

// Send trade notification to bot
function sendTradeNotification(notification) {
  try {
    let notifications = [];
    if (fs.existsSync(TRADE_NOTIFICATIONS_FILE)) {
      const content = fs.readFileSync(TRADE_NOTIFICATIONS_FILE, 'utf8').trim();
      if (content) {
        notifications = JSON.parse(content);
        if (!Array.isArray(notifications)) notifications = [];
      }
    }
    notifications.push({
      ...notification,
      source: 'gfair',
      timestamp: Date.now()
    });
    fs.writeFileSync(TRADE_NOTIFICATIONS_FILE, JSON.stringify(notifications, null, 2));
  } catch (err) {
    logError(`Failed to send trade notification: ${err.message}`);
  }
}

// ==================== TELEGRAM BOT INTEGRATION ====================
// Load bot configuration
const botConfig = { bot_token: process.env.TELEGRAM_BOT_TOKEN || '', admin_user_ids: process.env.TELEGRAM_ADMIN_ID ? [Number(process.env.TELEGRAM_ADMIN_ID)] : [] };

const BOT_TOKEN = botConfig.bot_token || '';
const ALLOWED_USER_ID = botConfig.admin_user_ids && botConfig.admin_user_ids.length > 0 ? botConfig.admin_user_ids[0] : 6103749905;
const TOKENS_FILE = path.join(__dirname, 'tokens.json');
const KEY_ALERT_FILE = path.join(__dirname, 'key_alert.json');
const DAILY_STATS_FILE = path.join(__dirname, 'daily_stats.json');
const ACCOUNT_BALANCES_FILE = path.join(__dirname, 'account_balances.json');

// Helper function to save tokens
function saveTokens(tokens, successMessage) {
  if (saveJson(TOKENS_FILE, tokens)) {
    return `${successMessage}\n\nИзменения будут применены при следующем обновлении (через 60 сек)`;
  }
  return null;
}

// Track sent alerts to avoid spam
let lastSpreadKeyAlert = 0;
const KEY_ALERT_COOLDOWN_MS = 3600000; // 1 hour between alerts

// Daily statistics tracking
let dailyStats = {
  date: new Date().toISOString().split('T')[0],
  trades: [],
  lastStatsSentAt: 0
};
const STATS_INTERVAL_MS = 24 * 60 * 60 * 1000; // 24 hours

// User conversation states for /add_token
const userStates = new Map();

// Menu navigation history for each user
const menuHistory = new Map();

// Create bot
let bot = null;
if (BOT_TOKEN) {
  try {
    bot = new TelegramBot(BOT_TOKEN, { polling: true });
    logInfo('🤖 Trading Bot Manager started');
    logInfo(`   Allowed user ID: ${ALLOWED_USER_ID}`);
  } catch (err) {
    logError(`Failed to initialize Telegram bot: ${err.message}`);
  }
}

// Authorization middleware
function isAuthorized(msg) {
  const isAuth = msg.from && msg.from.id === ALLOWED_USER_ID;
  if (!isAuth && msg.from) {
    logWarn(`Unauthorized access attempt from user ${msg.from.id} (${msg.from.username || 'no username'})`);
  }
  return isAuth;
}

// Load JSON file
function loadJson(filePath) {
  try {
    if (!fs.existsSync(filePath)) return [];
    const content = fs.readFileSync(filePath, 'utf8');
    return JSON.parse(content);
  } catch (err) {
    logError(`Error loading ${filePath}: ${err.message}`);
    return [];
  }
}

// Save JSON file
function saveJson(filePath, data) {
  try {
    fs.writeFileSync(filePath, JSON.stringify(data, null, 2));
    return true;
  } catch (err) {
    logError(`Error saving ${filePath}: ${err.message}`);
    return false;
  }
}

// Escape Markdown special characters
function escapeMarkdown(text) {
  if (typeof text !== 'string') return text;
  return text.replace(/([_*\[\]()~`>#+\-=|{}.!])/g, '\\$1');
}

// Load daily stats from file
function loadDailyStats() {
  try {
    if (fs.existsSync(DAILY_STATS_FILE)) {
      const data = JSON.parse(fs.readFileSync(DAILY_STATS_FILE, 'utf8'));
      const today = new Date().toISOString().split('T')[0];
      if (data.date === today) {
        dailyStats = data;
      } else {
        dailyStats = {
          date: today,
          trades: [],
          lastStatsSentAt: data.lastStatsSentAt || 0
        };
      }
    }
  } catch (err) {
    logError('Error loading daily stats:', err.message);
  }
}

// Save daily stats to file
function saveDailyStats() {
  try {
    fs.writeFileSync(DAILY_STATS_FILE, JSON.stringify(dailyStats, null, 2));
  } catch (err) {
    logError('Error saving daily stats:', err.message);
  }
}

// Track processed notifications to avoid duplicates
const processedNotifications = new Set();

// Process trade notifications from ggfair.js
function checkTradeNotifications() {
  try {
    if (!fs.existsSync(TRADE_NOTIFICATIONS_FILE)) return;
    
    const content = fs.readFileSync(TRADE_NOTIFICATIONS_FILE, 'utf8').trim();
    if (!content) return;
    
    const notifications = JSON.parse(content);
    if (!Array.isArray(notifications) || notifications.length === 0) return;
    
    // Process each notification with deduplication
    const uniqueNotifications = [];
    for (const notif of notifications) {
      const timestamp = notif.timestamp || Date.now();
      const roundedTimestamp = Math.floor(timestamp / 1000) * 1000;
      const uniqueKey = `${notif.source || 'unknown'}_${notif.symbol || 'unknown'}_${notif.type || 'unknown'}_${roundedTimestamp}`;
      
      if (processedNotifications.has(uniqueKey)) {
        continue;
      }
      
      processedNotifications.add(uniqueKey);
      uniqueNotifications.push(notif);
      
      sendTradeNotificationToTelegram(notif);
      
      dailyStats.trades.push({
        ...notif,
        processedAt: Date.now()
      });
    }
    
    // Clean up old processed notifications
    if (processedNotifications.size > 1000) {
      const entries = Array.from(processedNotifications);
      processedNotifications.clear();
      entries.slice(-500).forEach(key => processedNotifications.add(key));
    }
    
    fs.writeFileSync(TRADE_NOTIFICATIONS_FILE, '[]');
    saveDailyStats();
    
  } catch (err) {
    // Ignore parsing errors
  }
}

// Send trade notification to Telegram
function sendTradeNotificationToTelegram(notif) {
  if (!bot) return;
  try {
    let message = '';
    let source = '';
    
    if (notif.source === 'gfair' || notif.source === 'fair') {
      source = '📊 FAIR';
    } else if (notif.source === 'spread') {
      source = '📊 SPREAD';
    } else {
      source = '📊 TRADE';
    }
    
    if (notif.type === 'open') {
      const direction = notif.isLong ? '🟢 LONG' : '🔴 SHORT';
      message = `${source} | ${direction}

🪙 *Тикер:* \`${notif.symbol}\`
💰 *Маржа:* $${notif.margin?.toFixed(2) || '?'}
⚡ *Плечо:* ${notif.leverage}x
📈 *Цена входа:* ${notif.entryPrice?.toFixed(8) || '?'}`;
      
    } else if (notif.type === 'close') {
      const pnlEmoji = notif.pnl >= 0 ? '✅' : '❌';
      const pnlSign = notif.pnl >= 0 ? '+' : '';
      const pnlPctSign = notif.pnlPercent >= 0 ? '+' : '';
      message = `${source} | ЗАКРЫТО

🪙 *Тикер:* \`${notif.symbol}\`
${pnlEmoji} *PnL:* ${pnlSign}$${notif.pnl?.toFixed(2) || '?'} (${pnlPctSign}${notif.pnlPercent?.toFixed(2) || '?'}%)
📊 *Причина:* ${notif.reason || 'unknown'}`;
      
    } else if (notif.type === 'balance') {
      const accountType = notif.source === 'spot' ? '💵 SPOT' : '💰 FUTURES';
      message = `${accountType} | Баланс

💵 *Баланс:* $${notif.balance?.toFixed(2) || '?'} USDT`;
    }
    
    if (message) {
      bot.sendMessage(ALLOWED_USER_ID, message, { parse_mode: 'Markdown' });
    }
  } catch (err) {
    logError('Error sending trade notification to Telegram:', err.message);
  }
}

// Get futures account balance via WEB token (MEXC_KEY) - this is the only working method
async function getAccountBalance() {
  const url = 'https://contract.mexc.com/api/v1/private/account/assets';
  const payload = {};
  try {
    const sig = signReq(MEXC_KEY, payload);
    const headers = {
      "Accept": "application/json, text/plain, */*",
      "Accept-Language": "en-US,en;q=0.9",
      "Accept-Encoding": "gzip, deflate, br",
      "Content-Type": "application/json;charset=UTF-8",
      "Origin": "https://www.mexc.com",
      "Referer": "https://www.mexc.com/",
      "User-Agent": USER_AGENT,
      "Sec-Ch-Ua": '"Chromium";v="120", "Not_A Brand";v="8"',
      "Sec-Ch-Ua-Mobile": "?0",
      "Sec-Ch-Ua-Platform": '"Windows"',
      "Sec-Fetch-Dest": "empty",
      "Sec-Fetch-Mode": "cors",
      "Sec-Fetch-Site": "same-origin",
      "Authorization": MEXC_KEY,
      "x-mxc-sign": sig.sign,
      "x-mxc-nonce": sig.time
    };

    console.log('🔍 Fetching futures account balance...');
    const response = await axios.get(url, { headers, params: payload, timeout: 15000 });
    if (response.status !== 200) {
      console.error(`❌ Futures API Error: ${response.status} - ${response.statusText}`);
      return null;
    }

    const data = response.data;
    const assets = data?.data;
    if (!Array.isArray(assets)) {
      console.error('❌ Futures response missing data array:', JSON.stringify(data || {}).slice(0, 500));
      return null;
    }

    let usdtAvailable = 0;
    let usdtFrozen = 0;
    let activeBalances = 0;
    for (const asset of assets) {
      const currency = String(asset?.currency || asset?.asset || '').toUpperCase();
      const available = Number(asset?.availableBalance ?? 0);
      const frozen = Number(asset?.frozenBalance ?? 0);
      const total = available + frozen;
      if (Number.isFinite(total) && total > 0) activeBalances++;
      if (currency === 'USDT') {
        if (Number.isFinite(available)) usdtAvailable += available;
        if (Number.isFinite(frozen)) usdtFrozen += frozen;
      }
    }

    // Use available for trading, but it may be 0 while funds are frozen; still mark ready.
    available_balance = usdtAvailable;
    
    // Save balance to file for bot
    try {
      const balances = { futures: usdtAvailable, spot: null };
      fs.writeFileSync(ACCOUNT_BALANCES_FILE, JSON.stringify(balances, null, 2));
    } catch (err) {
      // Ignore errors
    }
    balanceReady = true;
    console.log(`✅ Futures balance updated: available=${usdtAvailable.toFixed(8)} USDT, frozen=${usdtFrozen.toFixed(8)} USDT, activeAssets=${activeBalances}`);
    return data;
  } catch (err) {
    console.error('❌ Futures balance fetch failed:', err.message || err);
    if (err?.response) {
      console.error(`Response status: ${err.response.status}`);
      console.error(`Response data:`, err.response.data);
      if (err.response.status === 401) {
        try {
          fs.writeFileSync(KEY_ALERT_FILE, JSON.stringify({ spread: true, fair: false, servers: {} }, null, 2));
        } catch (e) {
          logError(`Failed to write key alert: ${e.message}`);
        }
      }
    }
    return null;
  }
}


// Add ticker to blacklist file
function addToBlacklist(blacklistFile, ticker) {
  const normalized = ticker.toUpperCase().replace(/_USDT$/, '');
  const blacklist = loadJson(blacklistFile);
  
  if (!blacklist.includes(normalized)) {
    blacklist.push(normalized);
    if (saveJson(blacklistFile, blacklist)) {
      return { success: true, ticker: normalized };
    }
    return { success: false, error: 'Failed to save blacklist' };
  }
  
  return { success: true, ticker: normalized, alreadyExists: true };
}

// Remove ticker from blacklist file
function removeFromBlacklist(blacklistFile, ticker) {
  const normalized = normalizeBlacklistTicker(ticker);
  const blacklist = loadJson(blacklistFile);
  
  if (!Array.isArray(blacklist)) {
    logError(`Blacklist file ${blacklistFile} is not an array`);
    return { success: false, error: 'Blacklist file format error' };
  }
  
  let indexToRemove = -1;
  for (let i = 0; i < blacklist.length; i++) {
    const item = blacklist[i];
    const normalizedItem = normalizeBlacklistTicker(item);
    if (normalizedItem === normalized) {
      indexToRemove = i;
      break;
    }
  }
  
  if (indexToRemove !== -1) {
    blacklist.splice(indexToRemove, 1);
    if (saveJson(blacklistFile, blacklist)) {
      logInfo(`Removed ${normalized} from ${blacklistFile}`);
      return { success: true, ticker: normalized };
    }
    return { success: false, error: 'Failed to save blacklist' };
  }
  
  return { success: true, ticker: normalized, notFound: true };
}

// Credential updates are external to this research copy.
function updateApiKeysFile() { return { success: false, error: 'Credential file updates are disabled' }; }

// Stop PM2 process
function stopPm2Process(processName) {
  return new Promise((resolve) => {
    const { execFile } = require('child_process');
    execFile('pm2', ['stop', processName], (err, stdout, stderr) => {
      if (err) {
        logWarn(`Failed to stop PM2 process ${processName}: ${err.message}`);
        resolve(false);
        return;
      }
      logInfo(`Stopped PM2 process ${processName}`);
      resolve(true);
    });
  });
}

// Restart PM2 process
function restartPm2Process(processName) {
  return new Promise((resolve) => {
    const { execFile } = require('child_process');
    execFile('pm2', ['restart', processName], (err, stdout, stderr) => {
      if (err) {
        logWarn(`Failed to restart PM2 process ${processName}: ${err.message}`);
        resolve(false);
        return;
      }
      logInfo(`Restarted PM2 process ${processName}`);
      resolve(true);
    });
  });
}

function updateOrderbookReadyState(symbol, isReady) {
  const ob = orderbooks[symbol];
  if (!ob) return;
  if (isReady) {
    if (!ob._counted) {
      ob._counted = true;
      stats.orderbooksReady++;
    }
  } else if (ob._counted) {
    ob._counted = false;
    stats.orderbooksReady = Math.max(0, stats.orderbooksReady - 1);
  }
}

function markInFlight(symbol) {
  const now = Date.now();
  const rec = inFlightOpens.get(symbol) || { count: 0, ts: now };
  rec.count += 1;
  rec.ts = now;
  inFlightOpens.set(symbol, rec);
}

function clearInFlight(symbol) {
  if (inFlightOpens.has(symbol)) {
    const rec = inFlightOpens.get(symbol);
    rec.count = Math.max(0, rec.count - 1);
    if (rec.count === 0) {
      inFlightOpens.delete(symbol);
    } else {
      inFlightOpens.set(symbol, rec);
    }
  }
}

function ensureLastCloseStore(symbol) {
  if (!lastCloseTimes[symbol]) {
    lastCloseTimes[symbol] = { long: 0, short: 0 };
  }
  return lastCloseTimes[symbol];
}

function recordLastCloseTimestamp(symbol, isLong) {
  const store = ensureLastCloseStore(symbol);
  const key = isLong ? 'long' : 'short';
  store[key] = Date.now();
}

// Записать убыточное закрытие для GMGN (для отслеживания двух минусов подряд)
function recordGmgnLoss(symbol, isLong, pnlUsd) {
  if (!lastCloseLosses[symbol]) {
    lastCloseLosses[symbol] = [];
  }
  const losses = lastCloseLosses[symbol];
  const now = Date.now();
  
  // Добавить новое закрытие с убытком
  losses.push({ isLong, pnl: pnlUsd, timestamp: now });
  
  // Оставить только последние 3 закрытия
  if (losses.length > 3) {
    losses.shift();
  }
  
  // Проверить два минуса подряд с убытком > 6$
  if (losses.length >= 2) {
    const lastTwo = losses.slice(-2);
    const bothLosses = lastTwo.every(l => l.pnl < 0);
    const totalLoss = lastTwo.reduce((sum, l) => sum + Math.abs(l.pnl), 0);
    
    if (bothLosses && totalLoss > GMGN_CONSECUTIVE_LOSS_THRESHOLD_USD) {
      logWarn(`[GMGN] ${symbol}: Два минуса подряд с убытком $${totalLoss.toFixed(2)} > $${GMGN_CONSECUTIVE_LOSS_THRESHOLD_USD}. КД ${GMGN_CONSECUTIVE_LOSS_COOLDOWN_MS/1000} сек.`);
      // Установить кд для этого символа
      const store = ensureLastCloseStore(symbol);
      store[isLong ? 'long' : 'short'] = now;
    }
  }
  
  // Проверить два проигрыша подряд (любой убыток) - бан
  if (losses.length >= GMGN_CONSECUTIVE_LOSS_BAN_COUNT) {
    const lastTwo = losses.slice(-GMGN_CONSECUTIVE_LOSS_BAN_COUNT);
    const bothLosses = lastTwo.every(l => l.pnl < 0);
    
    if (bothLosses) {
      const normalizedSymbol = normalizeBlacklistTicker(symbol);
      if (normalizedSymbol && !STOPLOSS_BLACKLIST.has(normalizedSymbol)) {
        STOPLOSS_BLACKLIST.add(normalizedSymbol);
        BLACKLISTED_TICKERS.add(normalizedSymbol);
        persistStopLossBlacklist();
        logError(`[GMGN] ${symbol}: БАН - два проигрыша подряд!`);
        closeAllPositionsForSymbol(normalizedSymbol);
      }
    }
  }
}

// Проверить кд для двух минусов подряд
function isGmgnConsecutiveLossCooldownActive(symbol, isLong) {
  const store = lastCloseTimes[symbol];
  if (!store) return false;
  
  const lastCloseTs = store[isLong ? 'long' : 'short'] || 0;
  if (lastCloseTs === 0) return false;
  
  const now = Date.now();
  const timeSinceClose = now - lastCloseTs;
  
  // Проверить, был ли это кд от двух минусов подряд
  if (timeSinceClose < GMGN_CONSECUTIVE_LOSS_COOLDOWN_MS) {
    const losses = lastCloseLosses[symbol] || [];
    if (losses.length >= 2) {
      const lastTwo = losses.slice(-2);
      const bothLosses = lastTwo.every(l => l.pnl < 0);
      const totalLoss = lastTwo.reduce((sum, l) => sum + Math.abs(l.pnl), 0);
      
      if (bothLosses && totalLoss > GMGN_CONSECUTIVE_LOSS_THRESHOLD_USD) {
        return true;
      }
    }
  }
  
  return false;
}

function getLastCloseTimestamp(symbol, isLong) {
  const store = lastCloseTimes[symbol];
  if (!store) return 0;
  return store[isLong ? 'long' : 'short'] || 0;
}

function recordMexcPriceSample(symbol, bestBuy, bestSell) {
  if (bestBuy == null && bestSell == null) return;
  if (!mexcPriceHistory[symbol]) {
    mexcPriceHistory[symbol] = [];
  }
  const history = mexcPriceHistory[symbol];
  const now = Date.now();
  history.push({ time: now, bestBuy, bestSell });
  const cutoff = now - PRICE_HISTORY_RETENTION_MS;
  while (history.length > 0 && history[0].time < cutoff) {
    history.shift();
  }
}

function hasPriceMovedInDirection(symbol, isLong) {
  const history = mexcPriceHistory[symbol];
  if (!history || history.length < 2) return false;
  const now = Date.now();
  const windowStart = now - PRICE_TREND_WINDOW_MS;
  const latestEntry = history[history.length - 1];
  if (!latestEntry || latestEntry.time < windowStart) {
    return false;
  }

  let startEntry = null;
  for (const entry of history) {
    if (entry.time <= windowStart) {
      startEntry = entry;
    } else {
      break;
    }
  }

  if (!startEntry || startEntry.time > windowStart) {
    return false;
  }

  const startPrice = isLong ? startEntry.bestSell : startEntry.bestBuy;
  const endPrice = isLong ? latestEntry.bestSell : latestEntry.bestBuy;
  if (startPrice == null || endPrice == null) return false;

  return isLong ? endPrice > startPrice : endPrice < startPrice;
}

function getInFlightTotal() {
  const now = Date.now();
  let total = 0;
  for (const [sym, rec] of inFlightOpens.entries()) {
    if (now - rec.ts > INFLIGHT_TTL_MS) {
      inFlightOpens.delete(sym);
      continue;
    }
    total += rec.count;
  }
  return total;
}

function isOrderbookFresh(ob, nowTs) {
  if (!ob || !ob.depthTs) return false;
  return (nowTs - ob.depthTs) <= STALE_ORDERBOOK_MS;
}

function isTickerFresh(tickerTs, nowTs) {
  if (!tickerTs) return false;
  return (nowTs - tickerTs) <= STALE_TICKER_MS;
}

function shouldLogSpotArbSkip(key, cooldownMs = SPOT_ARB_SKIP_LOG_COOLDOWN_MS) {
  if (!key) return false;
  const now = Date.now();
  const last = spotArbSkipLogTs.get(key) || 0;
  if (now - last < cooldownMs) return false;
  spotArbSkipLogTs.set(key, now);
  return true;
}

function shouldLogGmgnSkip(key, cooldownMs = 30000) {
  if (!key) return false;
  const now = Date.now();
  const last = gmgnSkipLogTs.get(key) || 0;
  if (now - last < cooldownMs) return false;
  gmgnSkipLogTs.set(key, now);
  return true;
}

function logGmgnSkip(symbol, reason, extra = null, cooldownMs = 30000) {
  const safeSymbol = symbol || 'unknown';
  const key = `${safeSymbol}:${reason}`;
  if (!shouldLogGmgnSkip(key, cooldownMs)) return;
  if (extra && typeof extra === 'object') {
    logInfo(`[GMGN][SKIP] ${safeSymbol}: ${reason} | ${JSON.stringify(extra)}`);
  } else {
    logInfo(`[GMGN][SKIP] ${safeSymbol}: ${reason}`);
  }
}

function ensureOrderbookUpdaterStarted(symbol, source = '') {
  if (!symbol) return false;
  if (BLACKLISTED_SYMBOLS.has(symbol)) return false;
  if (!orderbooks[symbol]) {
    orderbooks[symbol] = {
      buy_orders: [],
      sell_orders: [],
      best_buy: null,
      best_sell: null,
      depthTs: null,
      _counted: false
    };
  }
  if (orderbookUpdatersStarted.has(symbol)) return false;
  orderbookUpdatersStarted.add(symbol);
  orderbookUpdater(symbol);
  const sourceSuffix = source ? ` (${source})` : '';
  logInfo(`📊 Started orderbook updater for ${symbol}${sourceSuffix}`);
  return true;
}

function hasLivePositionForSymbol(symbol) {
  const posMap = symbolPositions.get(symbol);
  if (!posMap) return false;
  for (const p of posMap.values()) {
    if (p && p.holdVol > 0 && !closed_positions.has(p.positionId || "")) return true;
  }
  return false;
}

function maybeClearStaleActiveTrade(symbol, reason = 'stale-no-position') {
  const trade = activeTrades.get(symbol);
  if (!trade) return false;
  if (inFlightOpens.has(symbol)) return false;
  if (hasLivePositionForSymbol(symbol)) return false;

  const now = Date.now();
  const lastPosTs = lastSymbolPositionUpdateTs.get(symbol) || 0;
  const posFresh = lastPosTs && (now - lastPosTs) <= POSITION_UPDATE_FRESH_MS;
  const ageMs = now - (trade.entryTime || 0);
  const closedById = trade.positionId && closed_positions.has(String(trade.positionId));

  if (closedById || (posFresh && ageMs >= ACTIVE_TRADE_STALE_GRACE_MS)) {
    finalizeActiveTrade(symbol, reason);
    return true;
  }

  if (ageMs >= ACTIVE_TRADE_STALE_MAX_AGE_MS) {
    finalizeActiveTrade(symbol, `${reason}-timeout`);
    return true;
  }

  return false;
}

// --- Slippage-based sizing helpers ---
function calcMaxNotionalForSide(levels, bestPx, maxBps, targetAvgPx, isLongSide = true, depthLimit = OB_SCAN_DEPTH_LEVELS, contractSize = 1) {
  if (!bestPx || !Array.isArray(levels) || levels.length === 0) return 0;
  const size = Number(contractSize) || 1;
  let cumQty = 0;
  let cumCost = 0;
  // Levels are expected to be sorted best -> worst (bids desc, asks asc)
  const dirLevels = levels;
  for (let i = 0; i < dirLevels.length && i < depthLimit; i++) {
    const [px, qty] = dirLevels[i];
    if (!px || !qty) continue;
    const levelQty = qty * size;
    const notional = px * levelQty;
    const newCumCost = cumCost + notional;
    const newCumQty = cumQty + levelQty;
    const avgPx = newCumCost / newCumQty;
    const within = isLongSide
      ? (avgPx - bestPx) / bestPx <= maxBps
      : (bestPx - avgPx) / bestPx <= maxBps;
    if (within) {
      cumCost = newCumCost;
      cumQty = newCumQty;
      continue;
    }
    // Partial fill of this level to stay at targetAvgPx
    const numerator = targetAvgPx * cumQty - cumCost;
    const denom = px - targetAvgPx;
    if (denom === 0) break;
    const qtyAdd = Math.min(levelQty, numerator / denom);
    if (qtyAdd > 0) {
      cumCost += px * qtyAdd;
      cumQty += qtyAdd;
    }
    break;
  }
  return cumCost; // notional in USDT
}

function computeMaxNotionalBySlippage(ob, maxSlippageBps, contractSize = 1) {
  if (!ob || !ob.best_buy || !ob.best_sell) return null;
  const maxBps = maxSlippageBps / 10000;
  const targetAskAvg = ob.best_sell * (1 + maxBps);
  const targetBidAvg = ob.best_buy * (1 - maxBps);
  const longNotional = calcMaxNotionalForSide(ob.sell_orders, ob.best_sell, maxBps, targetAskAvg, true, OB_SCAN_DEPTH_LEVELS, contractSize);
  const shortNotional = calcMaxNotionalForSide(ob.buy_orders, ob.best_buy, maxBps, targetBidAvg, false, OB_SCAN_DEPTH_LEVELS, contractSize);
  if (longNotional === 0 && shortNotional === 0) return null;
  const worst = Math.min(longNotional || Infinity, shortNotional || Infinity);
  return { longNotional, shortNotional, worst };
}

function computeDepthSlippageAtLimit(ob, depthLimit, contractSize = 1) {
  if (!ob || !ob.best_buy || !ob.best_sell) return null;
  const size = Number(contractSize) || 1;
  const take = (levels, limit, fromStart = true) => {
    const arr = fromStart ? levels : [...levels].reverse();
    let cumNotional = 0;
    let cumQty = 0;
    const len = Math.min(limit, arr.length);
    for (let i = 0; i < len; i++) {
      const [px, qty] = arr[i];
      if (!px || !qty) continue;
      const levelQty = qty * size;
      cumNotional += px * levelQty;
      cumQty += levelQty;
    }
    return { notional: cumNotional, qty: cumQty };
  };
  const ask = take(ob.sell_orders || [], depthLimit, true);
  const bid = take(ob.buy_orders || [], depthLimit, true);
  if (ask.qty === 0 || bid.qty === 0) return null;
  const vwapAsk = ask.notional / ask.qty;
  const vwapBid = bid.notional / bid.qty;
  const slipAsk = (vwapAsk - ob.best_sell) / ob.best_sell;
  const slipBid = (ob.best_buy - vwapBid) / ob.best_buy;
  const worstNotional = Math.min(ask.notional, bid.notional);
  return {
    longNotional: ask.notional,
    shortNotional: bid.notional,
    slipAsk,
    slipBid,
    worst: worstNotional
  };
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

// ---------------------- GMGN TP helpers (load configs, blacklist, filters) ----------------------
function normalizeBlacklistTicker(symbol = '') {
  return String(symbol || '').trim().toUpperCase().replace(/_USDT$/, '');
}

function isTickerBlacklisted(symbol = '') {
  const normalized = normalizeBlacklistTicker(symbol);
  return !!normalized && BLACKLISTED_TICKERS.has(normalized);
}

// Load blacklist from blacklist_fair.json (for FAIR strategy)
function loadFairBlacklistFromFile() {
  try {
    if (!fs.existsSync(BLACKLIST_FAIR_FILE)) {
      logInfo(`📂 blacklist_fair.json not found, using default blacklist`);
      return;
    }
    const raw = fs.readFileSync(BLACKLIST_FAIR_FILE, 'utf8');
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed)) {
      // Clear existing blacklist entries that might have been loaded before
      // But keep hardcoded ones
      const hardcoded = new Set(['BTC_MUSDT', 'BNBHOLDER_USDT', 'LISA_USDT', 'AVICI_USDT', '1_USDT']);
      BLACKLISTED_SYMBOLS.clear();
      for (const sym of hardcoded) {
        BLACKLISTED_SYMBOLS.add(sym);
      }
      // Add entries from file
      for (const sym of parsed) {
        const normalized = String(sym || '').trim().toUpperCase();
        if (normalized) {
          // Add both with and without _USDT suffix
          BLACKLISTED_SYMBOLS.add(normalized);
          if (!normalized.endsWith('_USDT')) {
            BLACKLISTED_SYMBOLS.add(`${normalized}_USDT`);
          }
        }
      }
      logInfo(`📂 Loaded ${parsed.length} tickers from blacklist_fair.json (total blacklisted: ${BLACKLISTED_SYMBOLS.size})`);
    }
  } catch (err) {
    logError(`Failed to load blacklist_fair.json: ${err.message}`);
  }
}

// Load blacklist from blacklist_spread.json (for GMGN strategy)
function loadSpreadBlacklistFromFile() {
  try {
    if (!fs.existsSync(BLACKLIST_SPREAD_FILE)) {
      logInfo(`📂 blacklist_spread.json not found, using default GMGN blacklist`);
      return;
    }
    const raw = fs.readFileSync(BLACKLIST_SPREAD_FILE, 'utf8');
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed)) {
      // Add entries from file to BLACKLISTED_TICKERS (used by GMGN strategy)
      for (const sym of parsed) {
        const normalized = normalizeBlacklistTicker(sym);
        if (normalized) {
          BLACKLISTED_TICKERS.add(normalized);
        }
      }
      logInfo(`📂 Loaded ${parsed.length} tickers from blacklist_spread.json (GMGN blacklist)`);
    }
  } catch (err) {
    logError(`Failed to load blacklist_spread.json: ${err.message}`);
  }
}

// Load stop-loss banlist from disk
function loadStopLossBlacklistFromFile() {
  try {
    if (!fs.existsSync(STOPLOSS_BLACKLIST_FILE)) return;
    const raw = fs.readFileSync(STOPLOSS_BLACKLIST_FILE, 'utf8');
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed)) {
      for (const sym of parsed) {
        const normalized = normalizeBlacklistTicker(sym);
        if (normalized) {
          STOPLOSS_BLACKLIST.add(normalized);
        }
      }
      logInfo(`📂 Loaded ${STOPLOSS_BLACKLIST.size} tickers from stop-loss banlist file`);
    }
  } catch (err) {
    logWarn(`Failed to load stop-loss banlist file: ${err.message}`);
  }
}

// Persist stop-loss banlist to disk
function persistStopLossBlacklist() {
  try {
    const payload = JSON.stringify(Array.from(STOPLOSS_BLACKLIST), null, 2);
    fs.writeFileSync(STOPLOSS_BLACKLIST_FILE, payload, 'utf8');
  } catch (err) {
    logWarn(`Failed to persist stop-loss banlist: ${err.message}`);
  }
}

// Record stop-loss outcome and return stop count and net loss
function recordStopLossOutcome(symbol, isStopLoss, pnlPct = null, isLong = false) {
  const normalized = normalizeBlacklistTicker(symbol);
  if (!normalized) return { stopCount: 0, netLoss: 0 };
  if (!stopLossHistory[normalized]) {
    stopLossHistory[normalized] = [];
  }
  const history = stopLossHistory[normalized];
  history.push(!!isStopLoss);
  while (history.length > STOPLOSS_HISTORY_SIZE) {
    history.shift();
  }
  const stopCount = history.reduce((count, hit) => count + (hit ? 1 : 0), 0);
  
  // Track PnL for LONG positions only
  let netLoss = 0;
  if (isLong && pnlPct !== null) {
    if (!longPnLHistory[normalized]) {
      longPnLHistory[normalized] = [];
    }
    const pnlHistory = longPnLHistory[normalized];
    pnlHistory.push(pnlPct);
    while (pnlHistory.length > STOPLOSS_HISTORY_SIZE) {
      pnlHistory.shift();
    }
    // Calculate net loss (sum of negative PnL)
    netLoss = pnlHistory.reduce((sum, pnl) => sum + (pnl < 0 ? Math.abs(pnl) : 0), 0);
  }
  
  return { stopCount, netLoss };
}

// Close only our open positions for a given symbol (used when ticker is banned). Do not close manual/external positions.
async function closeAllPositionsForSymbol(symbol) {
  const normalizedSymbol = normalizeBlacklistTicker(symbol);
  const fullSymbol = normalizedSymbol ? `${normalizedSymbol}_USDT` : symbol;
  const trade = getActiveTrade(fullSymbol);
  const ourPositionId = trade ? String(trade.positionId) : null;
  
  const symbolPosMap = symbolPositions.get(fullSymbol);
  if (!symbolPosMap || symbolPosMap.size === 0) return;
  
  for (const pos_id of symbolPosMap.keys()) {
    if (ourPositionId && String(pos_id) !== ourPositionId) continue;
    const pos = positions[pos_id];
    if (!pos || closed_positions.has(String(pos_id))) continue;
    if (!pos.holdVol || pos.holdVol <= 0) continue;
    
    logWarn(`🚫 Force closing our position ${pos_id} for banned ticker ${fullSymbol}`);
    try {
      await schedulePositionCloser(fullSymbol, pos, "market", true);
    } catch (err) {
      logError(`Failed to close position ${pos_id} for banned ticker ${fullSymbol}: ${err.message || err}`);
    }
  }
}

// Reload blacklist periodically (every 60 seconds)
function startFairBlacklistReloader() {
  setInterval(() => {
    loadFairBlacklistFromFile();
  }, 60000);
}

// Reload spread blacklist periodically (every 60 seconds)
function startSpreadBlacklistReloader() {
  setInterval(() => {
    loadSpreadBlacklistFromFile();
  }, 60000);
}

// Watch blacklist file for immediate updates
let fairBlacklistWatchDebounce = null;
function watchFairBlacklistFile() {
  try {
    if (!fs.existsSync(BLACKLIST_FAIR_FILE)) return;
    fs.watch(BLACKLIST_FAIR_FILE, (eventType) => {
      if (eventType === 'change') {
        // Debounce to avoid multiple reloads
        if (fairBlacklistWatchDebounce) clearTimeout(fairBlacklistWatchDebounce);
        fairBlacklistWatchDebounce = setTimeout(() => {
          logInfo('📂 blacklist_fair.json changed, reloading...');
          const oldBlacklist = new Set(BLACKLISTED_SYMBOLS);
          loadFairBlacklistFromFile();
          const newSize = BLACKLISTED_SYMBOLS.size;
          
          // Close positions for newly added tickers
          for (const symbol of BLACKLISTED_SYMBOLS) {
            if (!oldBlacklist.has(symbol)) {
              logWarn(`🚫 New ticker ${symbol} added to blacklist, closing positions...`);
              closeAllPositionsForSymbol(symbol);
            }
          }
          
          if (newSize > oldBlacklist.size) {
            logWarn(`🚫 New tickers added to blacklist. Total blacklisted: ${newSize}`);
          }
        }, 500);
      }
    });
  } catch (err) {
    logWarn(`Failed to watch blacklist_fair.json: ${err.message}`);
  }
}

// Watch spread blacklist file for immediate updates
let spreadBlacklistWatchDebounce = null;
function watchSpreadBlacklistFile() {
  try {
    if (!fs.existsSync(BLACKLIST_SPREAD_FILE)) return;
    fs.watch(BLACKLIST_SPREAD_FILE, (eventType) => {
      if (eventType === 'change') {
        // Debounce to avoid multiple reloads
        if (spreadBlacklistWatchDebounce) clearTimeout(spreadBlacklistWatchDebounce);
        spreadBlacklistWatchDebounce = setTimeout(() => {
          logInfo('📂 blacklist_spread.json changed, reloading...');
          const oldSize = BLACKLISTED_TICKERS.size;
          loadSpreadBlacklistFromFile();
          const newSize = BLACKLISTED_TICKERS.size;
          if (newSize > oldSize) {
            logWarn(`🚫 New tickers added to GMGN blacklist. Total blacklisted: ${newSize}`);
          }
        }, 500);
      }
    });
  } catch (err) {
    logWarn(`Failed to watch blacklist_spread.json: ${err.message}`);
  }
}

// Reload spread blacklist periodically (every 60 seconds)
function startSpreadBlacklistReloader() {
  setInterval(() => {
    loadSpreadBlacklistFromFile();
  }, 60000);
}

function _extractJsArrayLiteral(source, arrayStartIdx) {
  // Extracts a JS array literal starting at '[' and returns the substring including the matching ']'.
  let depth = 0;
  let inSingle = false;
  let inDouble = false;
  let inLineComment = false;
  let inBlockComment = false;

  for (let i = arrayStartIdx; i < source.length; i++) {
    const ch = source[i];
    const next = source[i + 1];

    if (inLineComment) {
      if (ch === '\n') inLineComment = false;
      continue;
    }
    if (inBlockComment) {
      if (ch === '*' && next === '/') {
        inBlockComment = false;
        i++;
      }
      continue;
    }

    if (inSingle) {
      if (ch === '\\') {
        i++;
        continue;
      }
      if (ch === '\'') inSingle = false;
      continue;
    }
    if (inDouble) {
      if (ch === '\\') {
        i++;
        continue;
      }
      if (ch === '"') inDouble = false;
      continue;
    }

    if (ch === '/' && next === '/') {
      inLineComment = true;
      i++;
      continue;
    }
    if (ch === '/' && next === '*') {
      inBlockComment = true;
      i++;
      continue;
    }
    if (ch === '\'') {
      inSingle = true;
      continue;
    }
    if (ch === '"') {
      inDouble = true;
      continue;
    }

    if (ch === '[') {
      depth++;
      continue;
    }
    if (ch === ']') {
      depth--;
      if (depth === 0) {
        return source.slice(arrayStartIdx, i + 1);
      }
      continue;
    }
  }
  throw new Error('Unterminated array literal while extracting TOKEN_CONFIGS');
}

function loadGmgnTokenConfigsFromFile() {
  // Load from tokens.json (same as spread.js)
  const tokensPath = path.join(__dirname, 'tokens.json');
  try {
    if (!fs.existsSync(tokensPath)) {
      throw new Error(`Missing ${tokensPath}`);
    }
    const raw = fs.readFileSync(tokensPath, 'utf8');
    const arr = JSON.parse(raw);
    if (!Array.isArray(arr)) {
      throw new Error('tokens.json is not an array');
    }
    const cleaned = arr
      .filter(x => x && typeof x === 'object')
      .map(x => ({
        mexc_name: String(x.mexc_name || '').trim(),
        gmgn_url: String(x.gmgn_url || '').trim(),
        margin_percent: Number(x.margin_percent ?? GMGN_DEFAULT_MARGIN_PERCENT ?? 10),
        leverage: Number(x.leverage ?? GMGN_DEFAULT_LEVERAGE ?? 5),
        percentagecountforopen: Number(x.percentagecountforopen ?? DEFAULT_OPEN_THRESHOLD ?? 7),
        normalDifferencePercent: Number(x.normalDifferencePercent ?? 1),
        normalSpreadClosure: Number(x.normalSpreadClosure ?? 0.5),
        maxDrawdown: Number(x.maxDrawdown ?? 8),
        takeProfitPercent: Number(x.takeProfitPercent ?? 5) // Default 5% TP
      }))
      .filter(x => x.mexc_name && x.gmgn_url);

    if (cleaned.length > 0) {
      logInfo(`[GMGN] Loaded ${cleaned.length} token configs from tokens.json`);
      return cleaned;
    }
    throw new Error('tokens.json parsed but yielded 0 valid entries');
  } catch (err) {
    logWarn(`[GMGN] Failed to load token configs from tokens.json: ${err.message || err}`);
  }

  logWarn('[GMGN] No GMGN token configs loaded - GMGN spread trading will be disabled.');
  return [];
}

// --- Deposit/withdraw status helpers (Spot API) -----------------------------------
function buildSpotQueryString(params) {
  return Object.keys(params)
    .map(k => `${encodeURIComponent(k)}=${encodeURIComponent(String(params[k]))}`)
    .join('&');
}

function signSpotRequest(params) {
  // IMPORTANT: signature must be calculated on the exact querystring order we send.
  // Do NOT sort keys here (it breaks endpoints that include multiple params like /order).
  const queryString = buildSpotQueryString(params);
  const signature = crypto
    .createHmac('sha256', MEXC_SPOT_API_SECRET)
    .update(queryString)
    .digest('hex');
  return { ...params, signature };
}

let mexcServerTimeOffsetCache = 0;
let mexcServerTimeOffsetLastSync = 0;
let mexcServerTimeOffsetSyncInFlight = null;
const MEXC_SERVER_TIME_SYNC_INTERVAL_MS = 60 * 1000; // 1 minute cache

async function syncMexcServerTime(forceSync = false) {
  // If not forcing sync, return cached value immediately (no HTTP requests during trading)
  if (!forceSync) {
    return mexcServerTimeOffsetCache;
  }

  // Force sync: make HTTP request to update cache
  if (mexcServerTimeOffsetSyncInFlight) {
    try {
      return await mexcServerTimeOffsetSyncInFlight;
    } catch (_) {
      // fallthrough to retry
    }
  }

  mexcServerTimeOffsetSyncInFlight = (async () => {
    try {
      const response = await axios.get(MEXC_TIME_URL, { timeout: 10000 });
      if (response.data && response.data.serverTime) {
        const serverTime = Number(response.data.serverTime);
        const localTime = Date.now();
        const offset = serverTime - localTime;
        mexcServerTimeOffsetCache = offset;
        mexcServerTimeOffsetLastSync = Date.now();
        logInfo(`⏰ Server time synced: offset=${offset}ms`);
        return offset;
      }
    } catch (err) {
      logWarn(`Failed to sync MEXC server time: ${err.message}`);
    }
    return mexcServerTimeOffsetCache || 0;
  })();

  try {
    return await mexcServerTimeOffsetSyncInFlight;
  } finally {
    mexcServerTimeOffsetSyncInFlight = null;
  }
}

async function fetchDepositWithdrawInfo() {
  if (!ENABLE_DEPOSIT_WITHDRAW_CHECK) return null;
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    logWarn('[GMGN][D/W] Spot API key/secret not configured - skipping deposit/withdraw check');
    return null;
  }

  const currentTime = Date.now();
  if (depositWithdrawCache && (currentTime - lastDepositWithdrawCacheUpdate) < DEPOSIT_WITHDRAW_CACHE_DURATION_MS) {
    return depositWithdrawCache;
  }

  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);

    const response = await axios.get(`${DEPOSIT_WITHDRAW_URL}?${queryString}`, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });

    if (response.data && Array.isArray(response.data)) {
      depositWithdrawCache = {};
      for (const item of response.data) {
        if (item.coin && item.networkList) {
          depositWithdrawCache[item.coin] = item.networkList;
        }
      }
      lastDepositWithdrawCacheUpdate = currentTime;
      logInfo(`[GMGN][D/W] ✅ Data updated: ${Object.keys(depositWithdrawCache).length} coins`);
      return depositWithdrawCache;
    }
  } catch (err) {
    logError(`[GMGN][D/W] ❌ Failed to fetch deposit/withdraw info: ${err.message}`);
  }

  return depositWithdrawCache; // return old cache if fetch failed
}

function isDepositWithdrawEnabled(coin, depositWithdrawData) {
  if (!depositWithdrawData || !depositWithdrawData[coin]) {
    return true; // assume enabled if no data
  }

  const networks = depositWithdrawData[coin];
  for (const network of networks) {
    const depositEnabled = network.depositEnable === true;
    const withdrawEnabled = network.withdrawEnable === true;
    if (depositEnabled && withdrawEnabled) return true;
  }
  return false;
}

async function buildDepositWithdrawBlacklist(symbols, isInitialCheck = true) {
  if (!ENABLE_DEPOSIT_WITHDRAW_CHECK) return { newlyBlocked: [], newlyUnblocked: [] };

  // Force cache refresh for periodic checks
  if (!isInitialCheck) {
    lastDepositWithdrawCacheUpdate = 0;
  }

  const depositWithdrawData = await fetchDepositWithdrawInfo();
  if (!depositWithdrawData) {
    logWarn('[GMGN][D/W] ⚠️ No deposit/withdraw data - allowing all tokens');
    return { newlyBlocked: [], newlyUnblocked: [] };
  }

  const previouslyBlocked = new Set(DEPOSIT_WITHDRAWAL_BLACKLIST);
  const currentlyBlocked = new Set();

  for (const symbol of symbols) {
    const coin = normalizeBlacklistTicker(symbol);
    if (!isDepositWithdrawEnabled(coin, depositWithdrawData)) {
      currentlyBlocked.add(coin);
    }
  }

  const newlyBlocked = [];
  for (const coin of currentlyBlocked) {
    if (!previouslyBlocked.has(coin)) {
      newlyBlocked.push(coin);
      const networks = depositWithdrawData[coin] || [];
      const networkStatus = networks.map(n => {
        const d = n.depositEnable ? '✅' : '❌';
        const w = n.withdrawEnable ? '✅' : '❌';
        return `${n.network}: D${d}/W${w}`;
      }).join(', ');
      logError(`[GMGN][D/W] 🚨 ${coin}_USDT: DEPOSIT/WITHDRAW CLOSED - trading blocked! [${networkStatus}]`);
    }
  }

  const newlyUnblocked = [];
  for (const coin of previouslyBlocked) {
    if (!currentlyBlocked.has(coin)) {
      newlyUnblocked.push(coin);
      logInfo(`[GMGN][D/W] ✅ ${coin}_USDT: Deposit/Withdraw reopened - trading resumed`);
    }
  }

  DEPOSIT_WITHDRAWAL_BLACKLIST.clear();
  for (const coin of currentlyBlocked) {
    DEPOSIT_WITHDRAWAL_BLACKLIST.add(coin);
  }

  if (isInitialCheck) {
    const totalTokens = symbols.length;
    const blockedCount = DEPOSIT_WITHDRAWAL_BLACKLIST.size;
    const enabledCount = totalTokens - blockedCount;
    logInfo(`${'='.repeat(60)}`);
    logInfo(`[GMGN][D/W] REPORT: total=${totalTokens} enabled=${enabledCount} blocked=${blockedCount}`);
    logInfo(`${'='.repeat(60)}`);
  } else if (newlyBlocked.length > 0 || newlyUnblocked.length > 0) {
    logInfo(`[GMGN][D/W] Update: newlyBlocked=${newlyBlocked.length} newlyUnblocked=${newlyUnblocked.length} totalBlocked=${DEPOSIT_WITHDRAWAL_BLACKLIST.size}`);
  }

  return { newlyBlocked, newlyUnblocked };
}

async function refreshDepositWithdrawStatusPeriodically() {
  if (!ENABLE_DEPOSIT_WITHDRAW_CHECK) return;
  await sleep(DEPOSIT_WITHDRAW_CHECK_INTERVAL_MS);
  while (true) {
    try {
      const symbols = gmgnTokenConfigs.map(cfg => cfg.mexc_name);
      const { newlyBlocked } = await buildDepositWithdrawBlacklist(symbols, false);
      if (newlyBlocked.length > 0) {
        logError(`[GMGN][D/W] ⚠️ Newly blocked: ${newlyBlocked.map(c => c + '_USDT').join(', ')}`);
      }
    } catch (err) {
      logWarn(`[GMGN][D/W] Periodic refresh failed: ${err.message || err}`);
    }
    await sleep(DEPOSIT_WITHDRAW_CHECK_INTERVAL_MS);
  }
}

function isDepositWithdrawBlacklisted(symbol = '') {
  const normalized = normalizeBlacklistTicker(symbol);
  return !!normalized && DEPOSIT_WITHDRAWAL_BLACKLIST.has(normalized);
}

// ---------------------- SPOT-FUTURES ARBITRAGE HELPERS ----------------------

// Fetch spot exchange info (available trading pairs)
async function fetchSpotExchangeInfo() {
  try {
    logInfo('[SPOT] Fetching spot exchange info...');
    const response = await axios.get('https://api.mexc.com/api/v3/exchangeInfo', { timeout: 15000 });
    const data = response.data;
    
    // Log response structure for debugging
    logInfo(`[SPOT] Response keys: ${Object.keys(data || {}).join(', ')}`);
    
    if (!data || !Array.isArray(data.symbols)) {
      logError('[SPOT] Invalid spot exchange info response - symbols is not an array');
      logError(`[SPOT] Response type: ${typeof data}, symbols type: ${typeof data?.symbols}`);
      logError(`[SPOT] Full response (first 1000 chars): ${JSON.stringify(data).slice(0, 1000)}`);
      return null;
    }
    
    logInfo(`[SPOT] Total symbols in response: ${data.symbols.length}`);
    
    // Log first symbol structure for debugging
    // Removed sample logging
    
    const usdtPairs = [];
    let statsSkipped = { noStatus: 0, notUsdt: 0, noSpot: 0, noSymbol: 0 };
    
    for (const sym of data.symbols) {
      const symbol = sym.symbol; // e.g., 'BTCUSDT'
      
      // Skip if no symbol
      if (!symbol) {
        statsSkipped.noSymbol++;
        continue;
      }
      
      // MEXC V3 uses 'status' field - check various formats
      // Values seen: 'ENABLED', '1', 1, 'BREAK', 'HALT'
      const status = sym.status;
      const statusOk = status === 'ENABLED' || status === 1 || status === '1' || status === 'TRADING';
      if (!statusOk) {
        statsSkipped.noStatus++;
        continue;
      }
      
      // Check if quote asset is USDT (MEXC uses quoteAsset or quoteCoin)
      const quoteAsset = sym.quoteAsset || sym.quoteCoin || '';
      if (quoteAsset !== 'USDT' && !symbol.endsWith('USDT')) {
        statsSkipped.notUsdt++;
        continue;
      }
      
      // For MEXC V3, most pairs are tradeable - be permissive
      // Only filter if explicitly marked as not allowed
      if (sym.isSpotTradingAllowed === false) {
        statsSkipped.noSpot++;
        continue;
      }
      
      // Extract base asset (MEXC uses baseAsset or baseCoin)
      const baseAsset = sym.baseAsset || sym.baseCoin || symbol.replace('USDT', '');
      
      if (!baseAsset) {
        statsSkipped.noSymbol++;
        continue;
      }
      
      // Extract trading rules from various possible formats
      let minQty = 0, maxQty = Infinity, stepSize = 0.00000001, minNotional = 0, tickSize = 0.00000001;
      
      // Try to get from baseSizePrecision/quotePrecision (MEXC V3 format)
      if (sym.baseSizePrecision !== undefined) {
        stepSize = Math.pow(10, -Number(sym.baseSizePrecision || 8));
      }
      if (sym.quotePrecision !== undefined) {
        tickSize = Math.pow(10, -Number(sym.quotePrecision || 8));
      }
      if (sym.quoteAmountPrecision !== undefined) {
        minNotional = Math.pow(10, -Number(sym.quoteAmountPrecision || 2));
      }
      
      // Also check filters array if present (Binance-style format)
      if (sym.filters && Array.isArray(sym.filters)) {
        for (const filter of sym.filters) {
          if (filter.filterType === 'LOT_SIZE') {
            minQty = Number(filter.minQty || 0);
            maxQty = Number(filter.maxQty || Infinity);
            stepSize = Number(filter.stepSize || stepSize);
          } else if (filter.filterType === 'MIN_NOTIONAL') {
            minNotional = Number(filter.minNotional || minNotional);
          } else if (filter.filterType === 'PRICE_FILTER') {
            tickSize = Number(filter.tickSize || tickSize);
          }
        }
      }
      
      // Use direct fields if available (MEXC format)
      if (sym.minQty !== undefined) minQty = Number(sym.minQty);
      if (sym.maxQty !== undefined) maxQty = Number(sym.maxQty);
      if (sym.minNotional !== undefined) minNotional = Number(sym.minNotional);
      
      spotSymbolDetails[symbol] = {
        baseAsset,
        quoteAsset: 'USDT',
        minQty,
        maxQty,
        stepSize,
        minNotional,
        tickSize
      };
      
      usdtPairs.push(symbol);
    }
    
    logInfo(`[SPOT] Found ${usdtPairs.length} USDT spot trading pairs out of ${data.symbols.length} total symbols`);
    logInfo(`[SPOT] Filtered out: noStatus=${statsSkipped.noStatus}, notUsdt=${statsSkipped.notUsdt}, noSpot=${statsSkipped.noSpot}, noSymbol=${statsSkipped.noSymbol}`);
    return usdtPairs;
  } catch (err) {
    logError(`[SPOT] Failed to fetch spot exchange info: ${err.message}`);
    if (err.response?.data) {
      logError(`[SPOT] API error response: ${JSON.stringify(err.response.data).slice(0, 500)}`);
    }
    return null;
  }
}

// Fetch spot account balance
async function fetchSpotAccountBalance() {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    logWarn('[SPOT] Spot API key/secret not configured');
    return null;
  }
  
  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);
    
    const response = await axios.get(`https://api.mexc.com/api/v3/account?${queryString}`, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });
    
    if (response.data && Array.isArray(response.data.balances)) {
      let usdtFree = 0;
      for (const bal of response.data.balances) {
        if (bal.asset === 'USDT') {
          usdtFree = Number(bal.free || 0);
          break;
        }
      }
      spotAvailableBalance = usdtFree;
      spotBalanceReady = true;
      logInfo(`[SPOT] Spot balance updated: ${usdtFree.toFixed(4)} USDT available`);
      saveBalancesToFile(); // Save to file for bot
      return usdtFree;
    }
  } catch (err) {
    logError(`[SPOT] Failed to fetch spot balance: ${err.message}`);
  }
  return null;
}

// Check deposit/withdraw status for spot symbols and update blacklist
async function updateSpotFuturesBlacklist(spotSymbolsList) {
  // Always keep static entries
  if (!ENABLE_DEPOSIT_WITHDRAW_CHECK) {
    spotFuturesBlacklist.clear();
    for (const s of SPOT_FUTURES_STATIC_BLACKLIST) spotFuturesBlacklist.add(s);
    return;
  }
  
  const depositWithdrawData = await fetchDepositWithdrawInfo();
  if (!depositWithdrawData) {
    logWarn('[SPOT] No deposit/withdraw data available');
    // Keep static entries even if we can't refresh D/W status
    spotFuturesBlacklist.clear();
    for (const s of SPOT_FUTURES_STATIC_BLACKLIST) spotFuturesBlacklist.add(s);
    return;
  }
  
  const previousBlocked = new Set(spotFuturesBlacklist);
  spotFuturesBlacklist.clear();
  for (const s of SPOT_FUTURES_STATIC_BLACKLIST) spotFuturesBlacklist.add(s);
  
  let newlyBlocked = 0;
  let newlyUnblocked = 0;
  
  for (const spotSymbol of spotSymbolsList) {
    const details = spotSymbolDetails[spotSymbol];
    if (!details) continue;
    
    const coin = details.baseAsset;
    if (!isDepositWithdrawEnabled(coin, depositWithdrawData)) {
      spotFuturesBlacklist.add(spotSymbol);
      if (!previousBlocked.has(spotSymbol)) {
        newlyBlocked++;
        logWarn(`[SPOT] 🚫 ${spotSymbol}: Deposit/Withdraw CLOSED - excluded from arbitrage`);
      }
    } else if (previousBlocked.has(spotSymbol) && !SPOT_FUTURES_STATIC_BLACKLIST.has(spotSymbol)) {
      newlyUnblocked++;
      logInfo(`[SPOT] ✅ ${spotSymbol}: Deposit/Withdraw REOPENED - enabled for arbitrage`);
    }
  }
  
  logInfo(`[SPOT] Blacklist update: blocked=${spotFuturesBlacklist.size}, newlyBlocked=${newlyBlocked}, newlyUnblocked=${newlyUnblocked}`);
}

// Scan spot market data and find arbitrage opportunities
async function scanSpotMarketData() {
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE) return;
  
  const now = Date.now();
  if (now - lastSpotMarketScanTime < SPOT_MARKET_SCAN_INTERVAL_MS) return;
  lastSpotMarketScanTime = now;
  
  logInfo('[SPOT] Starting spot market data scan...');
  
  // Fetch spot exchange info
  const spotPairs = await fetchSpotExchangeInfo();
  if (!spotPairs || spotPairs.length === 0) {
    logWarn('[SPOT] No spot pairs found');
    return;
  }
  
  // Find matching futures symbols FIRST - only track spot symbols with corresponding futures
  const matchingPairs = [];
  let filterStats = { noFutures: 0, futuresBlacklisted: 0, futuresNoMaxVol: 0, spotUntradeable: 0 };
  
  for (const spotSymbol of spotPairs) {
    const details = spotSymbolDetails[spotSymbol];
    if (!details) continue;
    
    // Convert spot symbol to futures symbol (e.g., BTCUSDT -> BTC_USDT)
    const futuresSymbol = `${details.baseAsset}_USDT`;
    
    // Check if futures contract exists
    if (!contract_details[futuresSymbol]) {
      filterStats.noFutures++;
      continue;
    }
    
    // Check if futures contract is blacklisted (includes maxVol=0 symbols)
    if (BLACKLISTED_SYMBOLS.has(futuresSymbol)) {
      filterStats.futuresBlacklisted++;
      continue;
    }
    
    // Check if futures has valid maxVol (not 0 or null)
    const futuresDetail = contract_details[futuresSymbol];
    const futuresMaxVol = futuresDetail?.maxVol;
    if (futuresMaxVol === null || futuresMaxVol === undefined || futuresMaxVol === 0 || isNaN(futuresMaxVol)) {
      filterStats.futuresNoMaxVol++;
      continue;
    }
    
    // Check if spot has valid trading params (minQty should be defined and > 0)
    // Note: maxQty = Infinity is OK (means no limit), but minQty = 0 or undefined means untradeable
    const spotMinQty = details.minQty;
    const spotMinNotional = details.minNotional;
    // Skip only if minQty is explicitly 0 AND minNotional is 0 (indicating untradeable)
    if (spotMinQty === 0 && spotMinNotional === 0) {
      filterStats.spotUntradeable++;
      continue;
    }
    
    matchingPairs.push({ spotSymbol, futuresSymbol, baseAsset: details.baseAsset });
  }
  
  logInfo(`[SPOT] Found ${matchingPairs.length} valid spot-futures pairs`);
  logInfo(`[SPOT] Filtered: noFutures=${filterStats.noFutures}, futuresBlacklisted=${filterStats.futuresBlacklisted}, futuresNoMaxVol=${filterStats.futuresNoMaxVol}, spotUntradeable=${filterStats.spotUntradeable}`);
  
  // Update spot symbols set - only include matching pairs
  const previousSpotSymbols = new Set(spotSymbols);
  spotSymbols = new Set(matchingPairs.map(p => p.spotSymbol));
  
  // Find new symbols
  const newSymbols = matchingPairs.filter(p => !previousSpotSymbols.has(p.spotSymbol));
  
  if (newSymbols.length > 0) {
    logInfo(`[SPOT] Found ${newSymbols.length} new spot-futures pairs`);
  }
  
  // Update deposit/withdraw blacklist - only for matching pairs
  const matchingSpotSymbols = matchingPairs.map(p => p.spotSymbol);
  await updateSpotFuturesBlacklist(matchingSpotSymbols);
  
  // Fetch spot balance
  await fetchSpotAccountBalance();
  
  // Filter out pairs with closed deposit/withdraw
  const tradablePairs = matchingPairs.filter(p => !spotFuturesBlacklist.has(p.spotSymbol));
  
  logInfo(`[SPOT] ${tradablePairs.length} pairs available for arbitrage (after D/W filter)`);
  
  // Collect new symbols that need subscription
  const newSymbolsToSubscribe = [];
  for (const { spotSymbol } of tradablePairs) {
    if (spotOrderbookUpdatersStarted.has(spotSymbol)) continue;

    // Initialize spot orderbook structure
    if (!spotOrderbooks[spotSymbol]) {
      spotOrderbooks[spotSymbol] = {
        bids: [],
        asks: [],
        best_bid: null,
        best_ask: null,
        depthTs: null
      };
    }

    spotOrderbookUpdatersStarted.add(spotSymbol);
    newSymbolsToSubscribe.push(spotSymbol);
  }

  // Prefer REST bookTicker poller for spot best bid/ask (WS is often blocked by MEXC)
  if (newSymbolsToSubscribe.length > 0) {
    logInfo(`[SPOT] Added ${newSymbolsToSubscribe.length} new symbols for spot bookTicker tracking`);
  }

  if (!ENABLE_SPOT_ORDERBOOK_WS && !spotBookTickerPollerRunning && tradablePairs.length > 0) {
    startSpotBookTickerPoller().catch(err => logWarn(`[SPOT] bookTicker poller exited: ${err.message || err}`));
  }

  // Optional: WS orderbooks (disabled by default)
  if (ENABLE_SPOT_ORDERBOOK_WS && !spotWsBlocked && newSymbolsToSubscribe.length > 0) {
    logInfo(`[SPOT] Starting WS orderbooks for ${newSymbolsToSubscribe.length} symbols`);
    startSpotOrderbookMultiplexer(newSymbolsToSubscribe);
  }
}

// Spot best-bid/ask updater via REST bookTicker (reliable fallback when WS is blocked)
async function startSpotBookTickerPoller() {
  if (spotBookTickerPollerRunning) return;
  spotBookTickerPollerRunning = true;
  logInfo(`[SPOT] Starting REST bookTicker poller (interval=${SPOT_BOOKTICKER_POLL_INTERVAL_MS}ms)`);

  while (spotBookTickerPollerRunning) {
    try {
      const resp = await axios.get(SPOT_BOOKTICKER_URL, { timeout: 15000 });
      const raw = resp?.data;
      const arr = Array.isArray(raw) ? raw : (raw ? [raw] : []);
      const now = Date.now();

      for (const item of arr) {
        const sym = item?.symbol;
        if (!sym) continue;
        if (!spotSymbols.has(sym)) continue;
        if (spotFuturesBlacklist.has(sym)) continue;

        const bid = Number(item.bidPrice);
        const ask = Number(item.askPrice);
        const bidQty = Number(item.bidQty) || 0;
        const askQty = Number(item.askQty) || 0;

        if (!spotOrderbooks[sym]) {
          spotOrderbooks[sym] = { bids: [], asks: [], best_bid: null, best_ask: null, depthTs: null };
        }
        const ob = spotOrderbooks[sym];
        ob.best_bid = Number.isFinite(bid) && bid > 0 ? bid : null;
        ob.best_ask = Number.isFinite(ask) && ask > 0 ? ask : null;
        ob.bids = ob.best_bid ? [[ob.best_bid, bidQty]] : [];
        ob.asks = ob.best_ask ? [[ob.best_ask, askQty]] : [];
        ob.depthTs = now;
      }

      spotBookTickerLastUpdate = now;
    } catch (err) {
      logWarn(`[SPOT] bookTicker poll error: ${err.message || err}`);
    }

    await sleep(SPOT_BOOKTICKER_POLL_INTERVAL_MS);
  }
}

// Place spot market buy order
async function placeSpotBuyOrder(symbol, quantity) {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    logError('[SPOT] Spot API credentials not configured');
    return null;
  }
  if (spotTradingDisabled) return null;
  
  try {
    // Prefer base-quantity for MARKET BUY to avoid MEXC "amount scale is invalid" errors on quoteOrderQty.
    const details = spotSymbolDetails[symbol];
    const stepSize = details?.stepSize || 0.00000001;
    const precision = Math.max(0, -Math.log10(stepSize));
    const adjustedQty = Math.floor(Number(quantity) / stepSize) * stepSize;
    const formattedQty = adjustedQty.toFixed(precision);

    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      symbol,
      side: 'BUY',
      type: 'MARKET',
      quantity: formattedQty,
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);
    
    const response = await axios.post(`https://api.mexc.com/api/v3/order?${queryString}`, null, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });
    
    if (response.data && response.data.orderId) {
      logInfo(`[SPOT] ✅ Spot BUY order placed: ${symbol} qty=${formattedQty} orderId=${response.data.orderId}`);
      return response.data;
    }
    
    logError(`[SPOT] Spot BUY order failed: ${JSON.stringify(response.data)}`);
    return null;
  } catch (err) {
    logError(`[SPOT] Spot BUY order error: ${err.message}`);
    if (err.response?.data) {
      logError(`[SPOT] API error: ${JSON.stringify(err.response.data)}`);
      const code = err.response.data?.code;
      const msg = String(err.response.data?.msg || '');
      if (code === 700002 || msg.toLowerCase().includes('signature')) {
        disableSpotTradingOnce(`Spot API signature invalid (code=${code})`);
      }
    }
    return null;
  }
}

// Place spot market sell order (to close position)
async function placeSpotSellOrder(symbol, quantity) {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    logError('[SPOT] Spot API credentials not configured');
    return null;
  }
  if (spotTradingDisabled) return null;
  
  try {
    const details = spotSymbolDetails[symbol];
    const stepSize = details?.stepSize || 0.00000001;
    const precision = Math.max(0, -Math.log10(stepSize));
    const adjustedQty = Math.floor(quantity / stepSize) * stepSize;
    const formattedQty = adjustedQty.toFixed(precision);
    
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      symbol,
      side: 'SELL',
      type: 'MARKET',
      quantity: formattedQty,
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);
    
    const response = await axios.post(`https://api.mexc.com/api/v3/order?${queryString}`, null, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });
    
    if (response.data && response.data.orderId) {
      logInfo(`[SPOT] ✅ Spot SELL order placed: ${symbol} qty=${formattedQty} orderId=${response.data.orderId}`);
      return response.data;
    }
    
    logError(`[SPOT] Spot SELL order failed: ${JSON.stringify(response.data)}`);
    return null;
  } catch (err) {
    logError(`[SPOT] Spot SELL order error: ${err.message}`);
    if (err.response?.data) {
      logError(`[SPOT] API error: ${JSON.stringify(err.response.data)}`);
      const code = err.response.data?.code;
      const msg = String(err.response.data?.msg || '');
      if (code === 700002 || msg.toLowerCase().includes('signature')) {
        disableSpotTradingOnce(`Spot API signature invalid (code=${code})`);
      }
    }
    return null;
  }
}

// Query spot order status by orderId
async function getSpotOrderStatus(symbol, orderId) {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    return null;
  }
  
  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      symbol,
      orderId,
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);
    
    const response = await axios.get(`https://api.mexc.com/api/v3/order?${queryString}`, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 10000
    });
    
    if (response.data) {
      return response.data;
    }
  } catch (err) {
    logError(`[SPOT] Failed to query order status: ${err.message}`);
    if (err.response?.data) {
      logError(`[SPOT] API error: ${JSON.stringify(err.response.data)}`);
    }
  }
  return null;
}

// Get spot balance for a specific asset
async function getSpotAssetBalance(asset) {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    return null;
  }
  
  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);
    
    const response = await axios.get(`https://api.mexc.com/api/v3/account?${queryString}`, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 10000
    });
    
    if (response.data && Array.isArray(response.data.balances)) {
      for (const bal of response.data.balances) {
        if (bal.asset === asset) {
          return {
            free: Number(bal.free || 0),
            locked: Number(bal.locked || 0),
            total: Number(bal.free || 0) + Number(bal.locked || 0)
          };
        }
      }
      // Asset not found = zero balance
      return { free: 0, locked: 0, total: 0 };
    }
  } catch (err) {
    logError(`[SPOT] Failed to fetch asset balance for ${asset}: ${err.message}`);
  }
  return null;
}

// Check for any remaining spot balance and attempt to sell (cleanup helper)
async function sellSpotRemainderIfAny(spotSymbol, reason = '', opts = {}) {
  if (!spotSymbol) return null;
  if (spotTradingDisabled) return null;
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) return null;

  const details = spotSymbolDetails[spotSymbol];
  if (!details) {
    logWarn(`[SPOT] Cannot check remaining balance for ${spotSymbol} - missing symbol details`);
    return null;
  }

  const baseAsset = opts.baseAsset || details.baseAsset;
  if (!baseAsset) {
    logWarn(`[SPOT] Cannot check remaining balance for ${spotSymbol} - missing base asset`);
    return null;
  }

  // Avoid selling if there's an active arbitrage position for this symbol
  for (const [, pos] of spotFuturesArbitragePositions) {
    if (pos?.spotSymbol === spotSymbol && pos?.status !== 'closed') {
      logWarn(`[SPOT] Skipping remainder sell for ${spotSymbol} - active arbitrage position`);
      return null;
    }
  }

  const delayMs = Math.max(0, Number(opts.delayMs) || 0);
  if (delayMs > 0) {
    await sleep(delayMs);
  }

  const balance = await getSpotAssetBalance(baseAsset);
  if (!balance) {
    logWarn(`[SPOT] Unable to fetch ${baseAsset} balance for remainder sell`);
    return null;
  }

  const free = Number(balance.free || 0);
  if (!(free > 0)) return null;

  const stepSize = details?.stepSize || 0.00000001;
  const precision = Math.max(0, -Math.log10(stepSize));
  const adjustedQty = Math.floor(free / stepSize) * stepSize;
  const formattedQty = adjustedQty.toFixed(precision);

  if (!(adjustedQty > 0)) return null;

  if (details?.minQty && adjustedQty < details.minQty) {
    logWarn(`[SPOT] Remaining ${baseAsset} ${formattedQty} below minQty ${details.minQty}, skipping sell`);
    return null;
  }

  const price = Number(spotOrderbooks?.[spotSymbol]?.best_bid || opts.price || 0);
  if (details?.minNotional && price > 0) {
    const notional = adjustedQty * price;
    if (notional < details.minNotional) {
      logWarn(`[SPOT] Remaining ${baseAsset} notional ${notional.toFixed(8)} below minNotional ${details.minNotional}, skipping sell`);
      return null;
    }
  }

  const reasonLabel = reason ? ` (${reason})` : '';
  logWarn(`[SPOT] ⚠️ Remaining ${baseAsset} detected${reasonLabel}: ${formattedQty}, attempting market sell...`);
  const result = await placeSpotSellOrder(spotSymbol, adjustedQty);
  if (!result) {
    logError(`[SPOT] ❌ Failed to sell remaining ${baseAsset}${reasonLabel}`);
  }
  return result;
}

// Verify spot order was actually filled - returns verified fill info or null
async function verifySpotOrderFill(symbol, orderId, expectedQty, baseAsset) {
  // Step 1: Try to get order update from WebSocket (fast path)
  if (spotUserWsConnected) {
    logInfo(`[SPOT] Checking order ${orderId} via WebSocket...`);

    const wsOrder = await waitForSpotOrderUpdate(orderId, (order) => {
      // MEXC spot private WS uses numeric status:
      // 1=Not traded, 2=Fully traded, 3=Partially traded, 4=Canceled, 5=Partially canceled
      const s = Number(order?.status);
      return s === 2 || s === 3 || s === 4 || s === 5;
    }, 2000, {
      // Allow a brief settle window to capture successive fills
      settleMs: 250,
      stopPredicate: (order) => {
        const s = Number(order?.status);
        return s === 2 || s === 4 || s === 5;
      }
    }); // Wait up to 2 seconds for WS update

    if (wsOrder) {
      const statusNum = Number(wsOrder.status);
      const statusLabel =
        statusNum === 2 ? 'FILLED' :
        statusNum === 3 ? 'PARTIALLY_FILLED' :
        statusNum === 4 ? 'CANCELED' :
        statusNum === 5 ? 'PARTIALLY_CANCELED' :
        `STATUS_${statusNum}`;

      // Prefer WS-native fields (strings): cumulativeQuantity / cumulativeAmount
      // Fallback: (quantity - remainQuantity)
      const cumQty = Number(wsOrder.cumulativeQuantity || 0);
      const cumAmt = Number(wsOrder.cumulativeAmount || 0);
      let executedQty = cumQty;
      if (!(executedQty > 0)) {
        const qty = Number(wsOrder.quantity || 0);
        const remain = Number(wsOrder.remainQuantity || 0);
        const diff = qty - remain;
        if (Number.isFinite(diff) && diff > 0) executedQty = diff;
      }
      const cummulativeQuoteQty = cumAmt;

      logInfo(`[SPOT] WS Order status: ${symbol} id=${orderId}, status=${statusLabel}(${statusNum}), executedQty=${executedQty}`);

      if (statusNum === 2 && executedQty > 0) {
        const avgPrice = cummulativeQuoteQty > 0 ? cummulativeQuoteQty / executedQty : 0;
        logInfo(`[SPOT] ✅ Order verified FILLED via WS: qty=${executedQty}, avgPrice=${avgPrice.toFixed(8)}`);
        return {
          verified: true,
          executedQty,
          avgPrice,
          cummulativeQuoteQty
        };
      }

      if (statusNum === 4 || statusNum === 5) {
        // If partially canceled but we already got most of the fill, accept it.
        if (executedQty >= expectedQty * 0.9) {
          const avgPrice = cummulativeQuoteQty > 0 ? cummulativeQuoteQty / executedQty : 0;
          logWarn(`[SPOT] ⚠️ Order ${statusLabel} but executedQty is sufficient (${executedQty}/${expectedQty}), accepting as complete`);
          return { verified: true, executedQty, avgPrice, cummulativeQuoteQty, wsPartialCancelAccepted: true };
        }
        logError(`[SPOT] ❌ Order was ${statusLabel} via WS: orderId=${orderId}, executedQty=${executedQty}`);
        return { verified: false, status: statusLabel, executedQty };
      }

      // PARTIALLY_FILLED - check if we have enough
      if (statusNum === 3) {
        if (executedQty >= expectedQty * 0.9) {
          const avgPrice = cummulativeQuoteQty > 0 ? cummulativeQuoteQty / executedQty : 0;
          logInfo(`[SPOT] ✅ Order partially filled via WS (${executedQty}/${expectedQty}), accepting as complete`);
          return { verified: true, executedQty, avgPrice, cummulativeQuoteQty };
        } else {
          logWarn(`[SPOT] ⚠️ Order partially filled via WS but insufficient: ${executedQty}/${expectedQty}`);
          return { verified: false, status: 'PARTIALLY_FILLED_INSUFFICIENT', executedQty };
        }
      }
    } else {
      logWarn(`[SPOT] No WS update for order ${orderId} within 2s`);
    }
  } else {
    logWarn(`[SPOT] User WS not connected, falling back to REST`);
  }

  // Step 2: Fallback - query order status via REST API
  const orderStatus = await getSpotOrderStatus(symbol, orderId);

  if (orderStatus) {
    logInfo(`[SPOT] REST Order status: ${symbol} id=${orderId}, status=${orderStatus.status}, executedQty=${orderStatus.executedQty}`);

    // Check if order is filled
    if (orderStatus.status === 'FILLED') {
      const executedQty = Number(orderStatus.executedQty || 0);
      const cummulativeQuoteQty = Number(orderStatus.cummulativeQuoteQty || 0);

      if (executedQty > 0) {
        const avgPrice = cummulativeQuoteQty > 0 ? cummulativeQuoteQty / executedQty : 0;
        logInfo(`[SPOT] ✅ Order verified FILLED via REST: qty=${executedQty}, avgPrice=${avgPrice.toFixed(8)}`);
        return {
          verified: true,
          executedQty,
          avgPrice,
          cummulativeQuoteQty
        };
      }
    }

    // Order exists but not filled (CANCELED, NEW, PARTIALLY_FILLED, etc.)
    if (orderStatus.status === 'CANCELED' || orderStatus.status === 'EXPIRED' || orderStatus.status === 'REJECTED') {
      logError(`[SPOT] ❌ Order was ${orderStatus.status} via REST: orderId=${orderId}`);
      return { verified: false, status: orderStatus.status, executedQty: Number(orderStatus.executedQty || 0) };
    }

    // Order is NEW or PARTIALLY_FILLED - check if sufficient
    if (orderStatus.status === 'PARTIALLY_FILLED') {
      const executedQty = Number(orderStatus.executedQty || 0);
      if (executedQty >= expectedQty * 0.9) {
        const cummulativeQuoteQty = Number(orderStatus.cummulativeQuoteQty || 0);
        const avgPrice = cummulativeQuoteQty > 0 ? cummulativeQuoteQty / executedQty : 0;
        logInfo(`[SPOT] ✅ Order partially filled via REST (${executedQty}/${expectedQty}), accepting as complete`);
        return { verified: true, executedQty, avgPrice, cummulativeQuoteQty };
      }
    }

    // Order still pending
    if (orderStatus.status === 'NEW' || orderStatus.status === 'PARTIALLY_FILLED') {
      logWarn(`[SPOT] ⚠️ Order still pending via REST: status=${orderStatus.status}, executedQty=${orderStatus.executedQty}`);
      return { verified: false, status: orderStatus.status, executedQty: Number(orderStatus.executedQty || 0) };
    }
  }

  // Step 3: Final fallback - verify by checking asset balance
  logInfo(`[SPOT] Order status queries inconclusive, verifying via balance check...`);

  const assetBalance = await getSpotAssetBalance(baseAsset);
  if (assetBalance) {
    logInfo(`[SPOT] ${baseAsset} balance: free=${assetBalance.free}, locked=${assetBalance.locked}, total=${assetBalance.total}`);

    // If we have at least 90% of expected quantity, consider it filled
    const minExpected = expectedQty * 0.9;
    if (assetBalance.free >= minExpected || assetBalance.total >= minExpected) {
      logInfo(`[SPOT] ✅ Balance verification passed: ${baseAsset} balance (${assetBalance.total}) >= expected (${minExpected})`);
      return {
        verified: true,
        executedQty: Math.min(assetBalance.free, expectedQty),
        avgPrice: 0, // Unknown from balance check
        cummulativeQuoteQty: 0,
        balanceVerified: true
      };
    } else {
      logError(`[SPOT] ❌ Balance verification failed: ${baseAsset} balance (${assetBalance.total}) < expected (${minExpected})`);
      return { verified: false, status: 'BALANCE_MISMATCH', actualBalance: assetBalance.total };
    }
  }

  logError(`[SPOT] ❌ Could not verify order fill - all verification methods failed`);
  return { verified: false, status: 'VERIFICATION_FAILED' };
}

// Spot user data WebSocket for order updates
let spotUserWs = null;
let spotUserWsConnected = false;
let spotUserWsListenKey = null;
let spotUserWsKeepaliveTimer = null;
let spotUserWsPingTimer = null;
let spotUserWsPongTimeout = null;
let spotUserWsReconnectTimer = null;
let spotUserWsLastStartAttemptTs = 0;
let spotUserWsLastMsgTs = 0;
let spotUserWsLastPongTs = 0;
let spotUserWsStartInFlight = null;

const SPOT_USER_WS_ENABLED = true;
const SPOT_USER_LISTENKEY_KEEPALIVE_MS = 20 * 60_000; // docs: valid 60min, extend via PUT
const SPOT_USER_WS_PING_INTERVAL_MS = 20_000;
const SPOT_USER_WS_PONG_TIMEOUT_MS = 10_000;
const SPOT_USER_WS_RECONNECT_MIN_MS = 2_000;
const SPOT_USER_WS_RECONNECT_MAX_MS = 60_000;
const SPOT_USER_WS_START_MIN_INTERVAL_MS = 1000; // prevent spam

// Event emitter for spot order updates
const spotUserOrderEvents = new (require('events').EventEmitter)();
const spotUserOrderUpdates = new Map();

// Protobuf decoder for spot user data
let spotUserPbRoot = null;
let spotUserPbWrapperType = null;
let spotUserPbAccountType = null;
let spotUserPbOrderType = null;
let spotUserPbEnabled = false;

// Initialize spot user data protobuf decoder
async function initSpotUserPbDecoder() {
  if (spotUserPbEnabled) return true;
  const fs = require('fs');
  const path = require('path');
  const protoPath = path.join(__dirname, 'user_ws.proto');
  if (!fs.existsSync(protoPath)) {
    console.log(`⚠️ user_ws.proto not found (${protoPath}), spot user WS disabled`);
    return false;
  }

  try {
    const protobuf = require('protobufjs');
    spotUserPbRoot = await protobuf.load(protoPath);

    // Spot user data types
    // NOTE: our local proto defines these types without a package.
    spotUserPbWrapperType = spotUserPbRoot.lookupType('PushDataV3ApiWrapper');
    spotUserPbAccountType = spotUserPbRoot.lookupType('PrivateAccountV3Api');
    spotUserPbOrderType = spotUserPbRoot.lookupType('PrivateOrdersV3Api');

    spotUserPbEnabled = true;
    console.log('✅ Spot user data protobuf decoder initialized');
    return true;
  } catch (err) {
    console.log(`⚠️ Spot user data protobuf decoder init failed: ${err.message}`);
    return false;
  }
}

// Decode spot user data protobuf wrapper
function decodeSpotUserPbWrapper(buf) {
  if (!spotUserPbEnabled || !spotUserPbWrapperType) return null;

  try {
    return spotUserPbWrapperType.decode(buf);
  } catch (err) {
    return null;
  }
}

// Check if buffer looks like JSON (for control messages)
function isJsonLikeBuffer(buf) {
  if (!Buffer.isBuffer(buf) || buf.length === 0) return false;
  const firstByte = buf[0];
  return firstByte === 0x7B || firstByte === 0x5B; // '{' or '['
}

// Safe JSON parse
function safeJsonParse(str) {
  try {
    return JSON.parse(str);
  } catch (_) {
    return null;
  }
}

// Convert protobuf Long to number safely
function toNumberMaybeLong(val) {
  if (typeof val === 'number') return val;
  if (val && typeof val === 'object' && val.low !== undefined) {
    return val.toNumber ? val.toNumber() : Number(val.low);
  }
  return 0;
}

// Create spot listen key for user data WS
async function createSpotListenKey() {
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    throw new Error('Spot API credentials not configured');
  }

  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);

    const response = await axios.post(`https://api.mexc.com/api/v3/userDataStream?${queryString}`, null, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });

    // Extract listenKey from various possible response formats
    const lk = response.data?.listenKey ?? response.data?.data?.listenKey ?? response.data?.data ?? response.data?.listen_key ?? null;
    if (lk) {
      logInfo(`[SPOT] ✅ Created listenKey for user data WS`);
      return String(lk);
    }

    throw new Error(`listenKey missing in response: ${JSON.stringify(response.data)}`);
  } catch (err) {
    logError(`[SPOT] Failed to create listenKey: ${err.message}`);
    throw err;
  }
}

// Keep alive spot listen key
async function keepAliveSpotListenKey(listenKey) {
  if (!listenKey || !MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) return;

  try {
    const serverTimeOffset = await syncMexcServerTime();
    const params = {
      listenKey,
      recvWindow: 60000,
      timestamp: Date.now() + serverTimeOffset
    };
    const signedParams = signSpotRequest(params);
    const queryString = buildSpotQueryString(signedParams);

    await axios.put(`https://api.mexc.com/api/v3/userDataStream?${queryString}`, null, {
      headers: {
        'X-MEXC-APIKEY': MEXC_SPOT_API_KEY,
        'Content-Type': 'application/json'
      },
      timeout: 15000
    });

    logInfo(`[SPOT] ✅ Extended listenKey lifetime`);
  } catch (err) {
    logError(`[SPOT] Failed to extend listenKey: ${err.message}`);
  }
}

// Upsert spot order from user WS
function upsertSpotOrderFromUserWs(orderObj, meta = {}) {
  const id = String(orderObj?.id || "").trim();
  if (!id) return;

  // Preserve wrapper metadata for later debugging
  try {
    if (meta && meta.symbol) orderObj._wsSymbol = String(meta.symbol);
    if (meta && meta.channel) orderObj._wsChannel = String(meta.channel);
  } catch (_) {}

  spotUserOrderUpdates.set(id, orderObj);
  const ts = Date.now();
  spotUserOrderEvents.emit(`order:${id}`, { order: orderObj, ts, ...meta });
  spotUserOrderEvents.emit("any", { orderId: id, order: orderObj, ts, ...meta });

  // Log order updates for debugging
  const status = orderObj.status;
  const executedQty = Number(orderObj.executedQty || orderObj.cumulativeQuantity || 0);
  const symbol = meta.symbol || 'UNKNOWN';

  logInfo(`[SPOT] 📥 WS Order update: ${symbol} id=${id} status=${status} executedQty=${executedQty}`);
}

// Wait for spot order update from WS
function waitForSpotOrderUpdate(orderId, predicate, timeoutMs = 5000, opts = {}) {
  const id = String(orderId || "").trim();
  if (!id) return Promise.resolve(null);
  const maxWait = Math.max(0, Number(timeoutMs) || 0);
  const settleMs = Math.max(0, Number(opts?.settleMs) || 0);
  const stopPredicate = typeof opts?.stopPredicate === 'function' ? opts.stopPredicate : null;

  // Fast-path: we already have a matching update
  const existing = spotUserOrderUpdates.get(id);
  if (existing && (!predicate || predicate(existing))) {
    if (stopPredicate && stopPredicate(existing)) return Promise.resolve(existing);
    if (!settleMs) return Promise.resolve(existing);
  }

  return new Promise((resolve) => {
    const start = Date.now();
    let lastMatch = (existing && (!predicate || predicate(existing))) ? existing : null;
    let timeoutTimer = null;
    let settleTimer = null;

    const cleanup = () => {
      try { spotUserOrderEvents.removeListener(`order:${id}`, onMsg); } catch (_) {}
      if (timeoutTimer) clearTimeout(timeoutTimer);
      if (settleTimer) clearTimeout(settleTimer);
    };

    const scheduleSettle = () => {
      if (!settleMs) return;
      if (settleTimer) clearTimeout(settleTimer);
      const elapsed = Date.now() - start;
      const remaining = maxWait - elapsed;
      const waitMs = Math.min(settleMs, Math.max(0, remaining));
      if (waitMs <= 0) {
        cleanup();
        resolve(lastMatch);
        return;
      }
      settleTimer = setTimeout(() => {
        cleanup();
        resolve(lastMatch);
      }, waitMs);
    };

    const onMsg = (evt) => {
      const ord = evt?.order;
      if (!ord) return;
      if (predicate && !predicate(ord)) return;
      lastMatch = ord;
      if (stopPredicate && stopPredicate(ord)) {
        cleanup();
        resolve(ord);
        return;
      }
      if (settleMs) {
        scheduleSettle();
        return;
      }
      cleanup();
      resolve(ord);
    };

    spotUserOrderEvents.on(`order:${id}`, onMsg);
    timeoutTimer = setTimeout(() => {
      cleanup();
      resolve(lastMatch);
    }, maxWait);

    if (settleMs && lastMatch) {
      scheduleSettle();
    }
  });
}

// Stop spot user data WS
function stopSpotUserDataWs(reason = "", opts = {}) {
  const full = Boolean(opts && opts.full);
  try {
    if (full) {
      if (spotUserWsKeepaliveTimer) clearInterval(spotUserWsKeepaliveTimer);
      spotUserWsKeepaliveTimer = null;
    }
  } catch (_) {}
  try {
    if (spotUserWsPingTimer) clearInterval(spotUserWsPingTimer);
    spotUserWsPingTimer = null;
  } catch (_) {}
  try {
    if (spotUserWsReconnectTimer) clearTimeout(spotUserWsReconnectTimer);
    spotUserWsReconnectTimer = null;
  } catch (_) {}
  try {
    if (spotUserWsPongTimeout) clearTimeout(spotUserWsPongTimeout);
    spotUserWsPongTimeout = null;
  } catch (_) {}

  // Allow future start attempts
  spotUserWsStartInFlight = null;

  spotUserWsConnected = false;
  if (spotUserWs) {
    try { spotUserWs.close(); } catch (_) {}
    try { spotUserWs.terminate(); } catch (_) {}
  }
  spotUserWs = null;

  if (reason) {
    logInfo(`[SPOT] 🛑 Spot user-data WS stopped (${reason})`);
  }
}

// Schedule reconnect for spot user WS
function scheduleSpotUserWsReconnect(reason) {
  if (spotUserWsReconnectTimer) return;

  let delay = SPOT_USER_WS_RECONNECT_MIN_MS;
  const lastAttempt = spotUserWsLastStartAttemptTs;
  if (lastAttempt > 0) {
    const timeSinceLast = Date.now() - lastAttempt;
    if (timeSinceLast < SPOT_USER_WS_RECONNECT_MIN_MS) {
      delay = Math.max(delay, SPOT_USER_WS_RECONNECT_MIN_MS - timeSinceLast);
    }
  }

  logInfo(`[SPOT] ⏰ Scheduling spot user WS reconnect in ${Math.round(delay/1000)}s (${reason})`);

  spotUserWsReconnectTimer = setTimeout(() => {
    spotUserWsReconnectTimer = null;
    startSpotUserDataWs("reconnect").catch(() => {});
  }, delay);
}

// DEBUG: Test spot user WS connection without trading
const DEBUG_TEST_SPOT_USER_WS = false; // Spot-futures strategy removed

// Start spot user data WebSocket
async function startSpotUserDataWs(reason = "start") {
  if (!SPOT_USER_WS_ENABLED) return false;
  // Allow WS testing even if trading is disabled
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE && !DEBUG_TEST_SPOT_USER_WS) return false;
  if (!MEXC_SPOT_API_KEY || !MEXC_SPOT_API_SECRET) {
    logError(`[SPOT] Cannot start user WS - API credentials not configured`);
    return false;
  }

  // Already connected
  if (spotUserWsConnected && spotUserWs && spotUserWs.readyState === WebSocket.OPEN) return true;

  // Rate-limit repeated start attempts
  const now = Date.now();
  if ((now - spotUserWsLastStartAttemptTs) < SPOT_USER_WS_START_MIN_INTERVAL_MS) {
    return false;
  }
  spotUserWsLastStartAttemptTs = now;

  // Dedupe concurrent start attempts
  if (spotUserWsStartInFlight) {
    try {
      return await spotUserWsStartInFlight;
    } catch (_) {
      // fallthrough to retry
    }
  }

  spotUserWsStartInFlight = (async () => {

  // Decoder is required to read order updates
  await initSpotUserPbDecoder();
  if (!spotUserPbEnabled) {
    logWarn(`[SPOT] Spot user-data WS disabled - protobuf decoder not available`);
    return false;
  }

  // Create listenKey if missing
  if (!spotUserWsListenKey) {
    try {
      spotUserWsListenKey = await createSpotListenKey();
    } catch (e) {
      logError(`[SPOT] ListenKey create failed: ${e?.message || e}`);
      scheduleSpotUserWsReconnect("listenKey create failed");
      return false;
    }
  }

  // Keepalive (extend listenKey) in the background
  if (!spotUserWsKeepaliveTimer) {
    spotUserWsKeepaliveTimer = setInterval(() => {
      keepAliveSpotListenKey(spotUserWsListenKey).catch(() => {});
    }, SPOT_USER_LISTENKEY_KEEPALIVE_MS);
  }

  // Connect to WebSocket (use wbs-api.mexc.com for private user data streams)
  const uri = `wss://wbs-api.mexc.com/ws?listenKey=${encodeURIComponent(spotUserWsListenKey)}`;
  logInfo(`[SPOT] 🔐 Connecting to user-data WS: ${uri.replace(spotUserWsListenKey, '***')}`);
  let ws;
  try {
    ws = new WebSocket(uri, { headers: { 'User-Agent': USER_AGENT }, perMessageDeflate: false });
  } catch (err) {
    logError(`[SPOT] WS connect error: ${err.message}`);
    scheduleSpotUserWsReconnect("connect error");
    return false;
  }

  spotUserWs = ws;

  return new Promise((resolve, reject) => {
    const timeout = setTimeout(() => {
      reject(new Error("WS connect timeout"));
    }, 10000);

    ws.on('open', () => {
      clearTimeout(timeout);
      spotUserWsConnected = true;
      logInfo(`[SPOT] ✅ Connected to spot user-data WS (${reason})`);

      // Subscribe to private order updates
      try {
        const subMsg = {
          method: "SUBSCRIPTION",
          params: [
            "spot@private.orders.v3.api.pb",
          ],
        };
        logInfo(`[SPOT] 📤 Sending subscription: ${JSON.stringify(subMsg)}`);
        ws.send(JSON.stringify(subMsg));
      } catch (err) {
        logError(`[SPOT] WS subscription error: ${err.message}`);
        reject(err);
        return;
      }

      // App-level ping
      if (!spotUserWsPingTimer) {
        spotUserWsPingTimer = setInterval(() => {
          try {
            if (!spotUserWs || spotUserWs.readyState !== WebSocket.OPEN) return;
            spotUserWs.send(JSON.stringify({ method: "PING" }));
            if (spotUserWsPongTimeout) clearTimeout(spotUserWsPongTimeout);
            spotUserWsPongTimeout = setTimeout(() => {
              try {
                logWarn(`[SPOT] WS pong timeout — reconnecting...`);
                stopSpotUserDataWs("pong-timeout");
                scheduleSpotUserWsReconnect("pong-timeout");
              } catch (_) {}
            }, SPOT_USER_WS_PONG_TIMEOUT_MS);
          } catch (_) {}
        }, SPOT_USER_WS_PING_INTERVAL_MS);
      }

      resolve(true);
    });

    ws.on('message', (raw) => {
      try {
        const buf = Buffer.isBuffer(raw) ? raw : Buffer.from(raw);
        spotUserWsLastMsgTs = Date.now();

        // JSON control messages (PONG / subscription acks / errors)
        if (isJsonLikeBuffer(buf)) {
          const msg = safeJsonParse(buf.toString("utf8"));
          if (!msg) return;

          const txt = typeof msg.msg === "string" ? msg.msg : "";
          const method = typeof msg.method === "string" ? msg.method : "";
          
          if (txt === "PONG" || method === "PONG") {
            spotUserWsLastPongTs = Date.now();
            if (spotUserWsPongTimeout) {
              clearTimeout(spotUserWsPongTimeout);
              spotUserWsPongTimeout = null;
            }
            return;
          }

          // Log subscription success
          if (txt && txt.toLowerCase().includes("subscribed successful")) {
            logInfo(`[SPOT] ✅ WS subscription confirmed: ${txt}`);
          }

          // Log subscription issues
          if (txt && txt.toLowerCase().includes("not subscribed successfully")) {
            logWarn(`[SPOT] ⚠️ WS subscription issue: ${txt}`);
          }
          
          // Log errors
          if (msg.code && msg.code !== 0) {
            logError(`[SPOT] ❌ WS error: code=${msg.code}, msg=${txt}`);
          }
          return;
        }

        // Binary protobuf
        const pb = decodeSpotUserPbWrapper(buf);
        if (!pb) return;

        const channel = String(pb.channel || "");

        if (pb.privateOrders) {
          const o = pb.privateOrders;
          upsertSpotOrderFromUserWs(o, { channel, symbol: pb.symbol });
          return;
        }

      } catch (err) {
        logError(`[SPOT] WS message error: ${err.message}`);
      }
    });

    ws.on('close', (code, reason) => {
      clearTimeout(timeout);
      const reasonStr = reason ? reason.toString() : '';
      logWarn(`[SPOT] 🔌 WS closed: code=${code}, reason=${reasonStr}`);
      spotUserWsConnected = false;
      stopSpotUserDataWs("close");
      scheduleSpotUserWsReconnect(`close:${code}`);
      resolve(false);
    });

    ws.on('error', (err) => {
      clearTimeout(timeout);
      logError(`[SPOT] ❌ WS error: ${err.message}`);
      if (err.code) logError(`[SPOT]    Error code: ${err.code}`);
      spotUserWsConnected = false;
      scheduleSpotUserWsReconnect("error");
      resolve(false);
    });

  });

  })();
}

// Spot orderbook WebSocket updater
// Multiplexed spot orderbook WebSocket connections
const SPOT_WS_MAX_SUBSCRIPTIONS_PER_SOCKET = 50; // Max symbols per WebSocket connection
const spotWsConnections = []; // Array of { ws, symbols: Set, pingInterval, isReady }

// Start multiplexed spot orderbook subscriptions
async function startSpotOrderbookMultiplexer(symbols) {
  if (spotWsBlocked) return;
  if (!symbols || symbols.length === 0) return;
  
  // Split symbols into chunks for multiple WebSocket connections
  const chunks = [];
  for (let i = 0; i < symbols.length; i += SPOT_WS_MAX_SUBSCRIPTIONS_PER_SOCKET) {
    chunks.push(symbols.slice(i, i + SPOT_WS_MAX_SUBSCRIPTIONS_PER_SOCKET));
  }
  
  logInfo(`[SPOT] Starting ${chunks.length} multiplexed WebSocket connections for ${symbols.length} symbols`);
  
  // Start each connection
  for (let i = 0; i < chunks.length; i++) {
    startSpotWsConnection(i, chunks[i]);
    // Small delay between connections to avoid rate limits
    await sleep(100);
  }
}

// Single multiplexed WebSocket connection handling multiple symbols
async function startSpotWsConnection(connIndex, symbolsChunk) {
  const uri = 'wss://wbs.mexc.com/ws';
  let backoff = 5000;
  let isFirstConnect = true;
  let lastLogTime = 0;
  
  while (true) {
    if (spotWsBlocked) return;
    let ws = null;
    let pingInterval = null;
    
    try {
      ws = new WebSocket(uri, { headers: { 'User-Agent': USER_AGENT } });
      
      ws.on('open', () => {
        backoff = 5000;
        
        // Subscribe to all symbols in this chunk
        const params = symbolsChunk.map(sym => `spot@public.limit.depth.v3.api@${sym}@${SPOT_ORDERBOOK_DEPTH}`);
        const sub = {
          method: 'SUBSCRIPTION',
          params: params
        };
        ws.send(JSON.stringify(sub));
        
        if (isFirstConnect) {
          logInfo(`[SPOT] 📊 WS#${connIndex}: Subscribed to ${symbolsChunk.length} orderbooks`);
          isFirstConnect = false;
        } else {
          const now = Date.now();
          if (now - lastLogTime > 60000) {
            logInfo(`[SPOT] 🔄 WS#${connIndex}: Reconnected (${symbolsChunk.length} symbols)`);
            lastLogTime = now;
          }
        }
      });
      
      ws.on('message', data => {
        try {
          const msg = JSON.parse(data.toString());

          // Handle pong messages
          if (msg.msg === 'PONG') {
            return;
          }

          // Handle subscription errors (MEXC often replies: "Not Subscribed successfully ... Reason: Blocked!")
          const msgText = typeof msg.msg === 'string' ? msg.msg : '';
          if (msgText.includes('Not Subscribed successfully')) {
            if (!spotWsBlockedLogged) {
              logError(`[SPOT] Spot WS subscription rejected by MEXC: ${msgText}`);
              spotWsBlockedLogged = true;
            }
            if (msgText.toLowerCase().includes('blocked')) {
              spotWsBlocked = true;
              // Close and stop reconnecting; REST bookTicker will keep spot prices updated
              try { ws.close(); } catch (_) {}
            }
            return;
          }

          // Handle subscription confirmation
          if ((msg.code === 0 || msg.code === 200) && msgText === 'success') return;

          // Handle depth updates - extract symbol from channel name
          if (msg.c && msg.c.includes('limit.depth') && msg.d) {
            // Channel format: spot@public.limit.depth.v3.api@BTCUSDT@5
            const parts = msg.c.split('@');
            const spotSymbol = parts.length >= 3 ? parts[2] : null;
            if (!spotSymbol) return;
            
            const bids = msg.d.bids || [];
            const asks = msg.d.asks || [];

            if (!spotOrderbooks[spotSymbol]) {
              spotOrderbooks[spotSymbol] = { bids: [], asks: [], best_bid: null, best_ask: null, depthTs: null };
            }

            const ob = spotOrderbooks[spotSymbol];
            ob.bids = bids.map(b => [Number(b.p), Number(b.v)]).sort((a, b) => b[0] - a[0]);
            ob.asks = asks.map(a => [Number(a.p), Number(a.v)]).sort((a, b) => a[0] - b[0]);
            ob.best_bid = ob.bids.length > 0 ? ob.bids[0][0] : null;
            ob.best_ask = ob.asks.length > 0 ? ob.asks[0][0] : null;
            ob.depthTs = Date.now();

            // Spot-futures strategy removed: no arbitrage hooks here
          }
        } catch (err) {
          // Silently ignore parse errors
        }
      });
      
      ws.on('error', err => {
        logWarn(`[SPOT] WS#${connIndex} error: ${err.message}`);
        try { ws.close(); } catch (_) {}
      });
      
      ws.on('close', () => {
        // Mark all symbols in this connection as disconnected
        for (const sym of symbolsChunk) {
          if (spotOrderbooks[sym]) {
            spotOrderbooks[sym].best_bid = null;
            spotOrderbooks[sym].best_ask = null;
            spotOrderbooks[sym].depthTs = null;
          }
        }
      });
      
      // MEXC requires ping every 30 seconds max, we do 15 to be safe
      // Format: {"method":"PING"} - MEXC official format
      pingInterval = setInterval(() => {
        try {
          if (ws && ws.readyState === WebSocket.OPEN) {
            ws.send(JSON.stringify({ method: 'PING' }));
          }
        } catch (_) {}
      }, 15000);
      
      await new Promise(resolve => ws.on('close', resolve));
    } catch (err) {
      logWarn(`[SPOT] WS#${connIndex} connect error: ${err.message}`);
    } finally {
      if (pingInterval) clearInterval(pingInterval);
      try { if (ws) ws.terminate(); } catch (_) {}
    }
    
    await sleep(backoff);
    backoff = Math.min(backoff * 2, 60000);
  }
}

// Legacy function for backwards compatibility - now uses multiplexer
async function startSpotOrderbookUpdater(spotSymbol) {
  // This function is now deprecated - use startSpotOrderbookMultiplexer instead
  // Keep for any direct calls, but it now does nothing as multiplexer handles all
}

// Check for spot-futures arbitrage opportunity
async function checkSpotFuturesArbitrage(spotSymbol) {
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE) return;
  if (spotTradingDisabled) return;
  if (!spotBalanceReady || spotAvailableBalance <= 0) return;
  
  // Skip if symbol is blacklisted
  if (spotFuturesBlacklist.has(spotSymbol)) return;
  
  const details = spotSymbolDetails[spotSymbol];
  if (!details) return;
  
  const futuresSymbol = `${details.baseAsset}_USDT`;
  
  // Check futures contract exists and not blacklisted
  if (!contract_details[futuresSymbol]) return;
  if (BLACKLISTED_SYMBOLS.has(futuresSymbol)) return;
  
  // Check max arbitrage positions
  if (spotFuturesArbitragePositions.size >= SPOT_FUTURES_MAX_POSITIONS) return;
  
  // Check if already have position for this pair (spot-futures arbitrage)
  for (const [, pos] of spotFuturesArbitragePositions) {
    if (pos.spotSymbol === spotSymbol || pos.futuresSymbol === futuresSymbol) {
      if (shouldLogSpotArbSkip(`spot-futures-active:${spotSymbol}`)) {
        logInfo(`[SPOT] Skipping ${spotSymbol} - already in spot-futures arbitrage position`);
      }
      return;
    }
  }

  // Check if symbol already has FAIR/GMGN position (prevent conflicts)
  const activeTrade = activeTrades.get(futuresSymbol) || activeTrades.get(spotSymbol);
  if (activeTrade) {
    if (shouldLogSpotArbSkip(`fair-gmgn-active:${spotSymbol}`)) {
      logInfo(`[SPOT] Skipping ${spotSymbol} - already has FAIR/GMGN position (${activeTrade.strategy}/${activeTrade.direction})`);
    }
    return;
  }
  
  // Get orderbooks
  const spotOb = spotOrderbooks[spotSymbol];
  const futuresOb = orderbooks[futuresSymbol];
  
  if (!spotOb || !spotOb.best_ask || !spotOb.depthTs) return;
  if (!futuresOb || !futuresOb.best_buy || !futuresOb.depthTs) return;
  
  // Check orderbook freshness
  const now = Date.now();
  if ((now - spotOb.depthTs) > STALE_ORDERBOOK_MS) return;
  if ((now - futuresOb.depthTs) > STALE_ORDERBOOK_MS) return;
  
  // Calculate spread: (futures bid - spot ask) / spot ask
  // If futures price > spot price, we can buy spot and short futures
  const spotAsk = spotOb.best_ask;
  const futuresBid = futuresOb.best_buy;
  
  const spread = (futuresBid - spotAsk) / spotAsk;

  // Track top spot-futures spreads continuously (not only when crossing open threshold)
  updateTopSpotFuturesSpreads(spotSymbol, futuresSymbol, spread);
  
  // Check if spread exceeds threshold
  if (spread < SPOT_FUTURES_OPEN_THRESHOLD) return;

  // Count spot-futures opportunities that passed threshold
  stats.opportunitiesFoundSpotFutures = (stats.opportunitiesFoundSpotFutures || 0) + 1;

  // Throttle open attempts (prevents spam when spread stays high)
  if (spotFuturesOpenInFlight) return;
  const lastAttempt = spotFuturesLastAttemptTs.get(spotSymbol) || 0;
  if ((now - lastAttempt) < SPOT_FUTURES_OPEN_ATTEMPT_COOLDOWN_MS) return;
  spotFuturesOpenInFlight = true;
  spotFuturesLastAttemptTs.set(spotSymbol, now);
  
  try {
    logInfo(`[SPOT] 🎯 Arbitrage opportunity: ${spotSymbol} spread=${(spread * 100).toFixed(2)}%`);
    logInfo(`[SPOT]    Spot ask: ${spotAsk}, Futures bid: ${futuresBid}`);
    
    // Execute arbitrage trade
    await executeSpotFuturesArbitrage(spotSymbol, futuresSymbol, spotAsk, futuresBid, spread);
  } finally {
    spotFuturesOpenInFlight = false;
  }
}

// Execute spot-futures arbitrage trade
async function executeSpotFuturesArbitrage(spotSymbol, futuresSymbol, spotPrice, futuresPrice, spread) {
  const details = spotSymbolDetails[spotSymbol];
  if (!details) return;
  
  // Check futures balance is ready
  if (!balanceReady || !Number.isFinite(available_balance) || available_balance <= 0) {
    logWarn(`[SPOT] Futures balance not ready or insufficient`);
    return;
  }
  
  // Calculate trade size (USDT value) based on position index
  // 1st position: 25% spot OR 25% futures (min)
  // 2nd position: 33.33% spot OR 25% futures (min)
  // 3rd position: 50% spot OR 25% futures (min)
  // 4th position: 100% spot OR 25% futures (min)
  const positionIndex = spotFuturesArbitragePositions.size;
  let spotPercent;
  if (positionIndex === 0) {
    spotPercent = 0.25; // 25%
  } else if (positionIndex === 1) {
    spotPercent = 1/3; // 33.33%
  } else if (positionIndex === 2) {
    spotPercent = 0.5; // 50%
  } else {
    spotPercent = 1.0; // 100%
  }
  
  const spotValue = spotAvailableBalance * spotPercent;
  const futuresValue = available_balance * 0.25; // Always 25% of futures balance
  const tradeValue = Math.min(spotValue, futuresValue);
  
  if (tradeValue < details.minNotional) {
    logWarn(`[SPOT] Trade value ${tradeValue.toFixed(4)} below minNotional ${details.minNotional} (spot: ${spotValue.toFixed(4)}, futures: ${futuresValue.toFixed(4)})`);
    return;
  }
  
  // Calculate spot quantity (base asset) and ensure notional after step rounding is still valid
  const spotQty = tradeValue / spotPrice;
  const adjustedSpotQty = Math.floor(spotQty / details.stepSize) * details.stepSize;
  const estNotional = adjustedSpotQty * spotPrice;
  if (estNotional < details.minNotional) {
    logWarn(`[SPOT] Estimated notional ${estNotional.toFixed(4)} below minNotional ${details.minNotional} after step rounding`);
    return;
  }
  
  if (adjustedSpotQty < details.minQty) {
    logWarn(`[SPOT] Spot qty ${adjustedSpotQty} below minQty ${details.minQty}`);
    return;
  }
  
  // Calculate futures volume (must match spot value)
  const contractSize = contract_sizes[futuresSymbol];
  if (!contractSize) {
    logError(`[SPOT] No contract size for ${futuresSymbol}`);
    return;
  }
  
  const [priceScale, volScale, maxVol] = getSymbolScale(futuresSymbol);
  const futuresVol = (adjustedSpotQty * spotPrice) / (futuresPrice * contractSize);
  const adjustedFuturesVol = adjustVol(futuresVol, volScale);
  
  if (adjustedFuturesVol <= 0) {
    logWarn(`[SPOT] Futures volume too small`);
    return;
  }
  
  if (maxVol !== null && adjustedFuturesVol > maxVol) {
    logWarn(`[SPOT] Futures volume ${adjustedFuturesVol} exceeds maxVol ${maxVol}`);
    return;
  }
  
  const arbitrageId = `ARB_${Date.now()}_${details.baseAsset}`;
  logInfo(`[SPOT] 🚀 Opening arbitrage position ${arbitrageId} (#${positionIndex + 1})`);
  logInfo(`[SPOT]    Balance allocation: ${(spotPercent * 100).toFixed(1)}% spot (${spotValue.toFixed(4)} USDT) OR 25% futures (${futuresValue.toFixed(4)} USDT) = ${tradeValue.toFixed(4)} USDT`);
  logInfo(`[SPOT]    Spot BUY: ${spotSymbol} qty=${adjustedSpotQty.toFixed(8)} @ ~${spotPrice}`);
  logInfo(`[SPOT]    Futures SHORT: ${futuresSymbol} vol=${adjustedFuturesVol} @ ~${futuresPrice}`);
  
  // Step 1: Place spot buy order (use base quantity for reliability)
  const spotOrder = await placeSpotBuyOrder(spotSymbol, adjustedSpotQty);
  if (!spotOrder) {
    logError(`[SPOT] ❌ Failed to place spot buy order, aborting arbitrage`);
    return;
  }
  
  // CRITICAL: Verify the spot order was actually filled before proceeding
  // Don't trust the initial response alone - query order status and/or balance
  let filledSpotQty = 0;
  let avgSpotPrice = spotPrice;
  let quoteSpent = 0;
  
  // Check initial response first
  const initialExecutedQty = Number(spotOrder.executedQty || 0);
  const initialQuoteSpent = Number(spotOrder.cummulativeQuoteQty || 0);
  const initialStatus = spotOrder.status;
  
  logInfo(`[SPOT] Initial order response: status=${initialStatus}, executedQty=${initialExecutedQty}, cummulativeQuoteQty=${initialQuoteSpent}`);
  
  // If response shows FILLED and executedQty > 0, we can trust it
  if (initialStatus === 'FILLED' && initialExecutedQty > 0) {
    filledSpotQty = initialExecutedQty;
    quoteSpent = initialQuoteSpent;
    avgSpotPrice = (quoteSpent > 0 && filledSpotQty > 0) ? (quoteSpent / filledSpotQty) : spotPrice;
    logInfo(`[SPOT] ✅ Spot order filled (from response): qty=${filledSpotQty}, avgPrice=${avgSpotPrice.toFixed(8)}`);
  } else {
    // Response doesn't confirm fill - verify via order query (no artificial delay)
    logWarn(`[SPOT] ⚠️ Order response uncertain (status=${initialStatus}, executedQty=${initialExecutedQty}), verifying...`);
    
    const verifyResult = await verifySpotOrderFill(spotSymbol, spotOrder.orderId, adjustedSpotQty, details.baseAsset);
    
    if (!verifyResult || !verifyResult.verified) {
      const reason = verifyResult?.status || 'UNKNOWN';
      logError(`[SPOT] ❌ Spot order NOT filled (reason: ${reason}), aborting arbitrage!`);
      logError(`[SPOT]    Order may have been cancelled by exchange. orderId=${spotOrder.orderId}`);
      await sellSpotRemainderIfAny(spotSymbol, `abort:${reason}`, {
        baseAsset: details.baseAsset,
        price: spotPrice,
        delayMs: 200
      });
      // Cleanup any unexpected spot balance from partial fills
      return;
    }
    
    filledSpotQty = verifyResult.executedQty;
    quoteSpent = verifyResult.cummulativeQuoteQty || 0;
    avgSpotPrice = verifyResult.avgPrice > 0 ? verifyResult.avgPrice : spotPrice;
    
    if (verifyResult.balanceVerified) {
      logInfo(`[SPOT] ✅ Spot order verified via balance check: qty=${filledSpotQty}`);
    } else {
      logInfo(`[SPOT] ✅ Spot order verified: qty=${filledSpotQty}, avgPrice=${avgSpotPrice.toFixed(8)}`);
    }
  }
  
  // Final sanity check - if filledSpotQty is 0 or too small, abort
  if (filledSpotQty <= 0 || filledSpotQty < adjustedSpotQty * 0.5) {
    logError(`[SPOT] ❌ Filled quantity too low (${filledSpotQty} vs expected ${adjustedSpotQty}), aborting arbitrage`);
    await sellSpotRemainderIfAny(spotSymbol, 'abort:filled-too-low', {
      baseAsset: details.baseAsset,
      price: avgSpotPrice,
      delayMs: 200
    });
    return;
  }
  
  // Recalculate futures volume based on actual spot fill
  const actualFuturesVol = (filledSpotQty * avgSpotPrice) / (futuresPrice * contractSize);
  const finalFuturesVol = adjustVol(actualFuturesVol, volScale);
  
  // Step 2: Place futures short order
  const futuresOrder = {
    symbol: futuresSymbol,
    side: 3, // SHORT
    openType: SPOT_FUTURES_MARGIN_TYPE, // Cross margin
    type: '5', // Market
    vol: finalFuturesVol,
    leverage: SPOT_FUTURES_LEVERAGE,
    priceProtect: '0',
    ts: Date.now(),
    marketCeiling: 'false'
  };
  
  const futuresResp = await placeOrder(MEXC_KEY, futuresOrder);
  
  if (!futuresResp || !futuresResp.success) {
    logError(`[SPOT] ❌ Failed to place futures short, closing spot position immediately!`);
    logError(`[SPOT]    Futures error: ${JSON.stringify(futuresResp)}`);
    
    // Emergency: sell spot position
    await placeSpotSellOrder(spotSymbol, filledSpotQty);
    await sellSpotRemainderIfAny(spotSymbol, 'abort:futures-short-failed', {
      baseAsset: details.baseAsset,
      price: avgSpotPrice,
      delayMs: 250
    });
    return;
  }
  
  logInfo(`[SPOT] ✅ Futures SHORT order placed: ${JSON.stringify(futuresResp)}`);
  
  // Register arbitrage position
  const position = {
    arbitrageId,
    spotSymbol,
    futuresSymbol,
    spotQty: filledSpotQty,
    futuresVol: finalFuturesVol,
    spotEntryPrice: avgSpotPrice,
    futuresEntryPrice: futuresPrice, // Will be updated from WS
    openSpread: spread,
    openTime: Date.now(),
    status: 'open',
    closePending: false
  };
  
  spotFuturesArbitragePositions.set(arbitrageId, position);
  stats.spotFuturesTradesOpened = (stats.spotFuturesTradesOpened || 0) + 1;
  
  // Send open notification for spot-futures arbitrage
  sendTradeNotification({
    type: 'open',
    symbol: `${spotSymbol}/${futuresSymbol}`,
    isLong: false, // Always short futures in arbitrage
    margin: tradeValue,
    leverage: SPOT_FUTURES_LEVERAGE,
    entryPrice: futuresPrice,
    strategy: 'spot-futures'
  });
  
  logInfo(`[SPOT] 🎉 Arbitrage position opened: ${arbitrageId}`);
  logInfo(
    `[SPOT]    Open spread: ${(spread * 100).toFixed(2)}%, target close spread: ` +
    `${(SPOT_FUTURES_CLOSE_THRESHOLD_SHORT * 100).toFixed(2)}% (<${(SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS / 1000 / 60).toFixed(0)}m) / ` +
    `${(SPOT_FUTURES_CLOSE_THRESHOLD_LONG * 100).toFixed(2)}% (>=${(SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS / 1000 / 60).toFixed(0)}m)`
  );
  
  // Refresh spot balance
  await fetchSpotAccountBalance();
}

// Event-driven close check: called from spot/futures orderbook message handlers
async function checkSpotFuturesArbitrageCloseOnOrderbookUpdate(updatedSymbol, triggerSource = '') {
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE) return;
  if (!updatedSymbol) return;
  if (spotFuturesArbitragePositions.size === 0) return;

  for (const [arbitrageId, position] of spotFuturesArbitragePositions) {
    if (position.status !== 'open' || position.closePending) continue;
    if (position.spotSymbol !== updatedSymbol && position.futuresSymbol !== updatedSymbol) continue;

    const { spotSymbol, futuresSymbol, spotQty, futuresVol, spotEntryPrice, futuresEntryPrice, openTime } = position;

    const spotOb = spotOrderbooks[spotSymbol];
    const futuresOb = orderbooks[futuresSymbol];
    if (!spotOb || !spotOb.best_bid) continue;
    if (!futuresOb || !futuresOb.best_sell) continue;

    const spotBid = spotOb.best_bid;        // price to sell spot
    const futuresAsk = futuresOb.best_sell; // price to close short
    if (!Number.isFinite(spotBid) || spotBid <= 0) continue;
    if (!Number.isFinite(futuresAsk) || futuresAsk <= 0) continue;

    const currentSpread = (futuresAsk - spotBid) / spotBid;

    const spotPnl = (spotBid - spotEntryPrice) * spotQty;
    const futuresPnl = (futuresEntryPrice - futuresAsk) * futuresVol * (contract_sizes[futuresSymbol] || 1);
    const totalPnl = spotPnl + futuresPnl;
    const pnlPercent = totalPnl / (spotEntryPrice * spotQty);
    const elapsed = Date.now() - openTime;
    const closeThreshold = elapsed < SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS
      ? SPOT_FUTURES_CLOSE_THRESHOLD_SHORT
      : SPOT_FUTURES_CLOSE_THRESHOLD_LONG;

    let shouldClose = false;
    let closeReason = '';

    // Check spread convergence
    if (currentSpread <= closeThreshold) {
      shouldClose = true;
      closeReason = `spread-converged (${(currentSpread * 100).toFixed(2)}% <= ${(closeThreshold * 100).toFixed(2)}%)`;
    }

    // Check max drawdown (disabled when <= 0)
    if (SPOT_FUTURES_MAX_DRAWDOWN_PERCENT > 0 && pnlPercent <= -SPOT_FUTURES_MAX_DRAWDOWN_PERCENT) {
      shouldClose = true;
      closeReason = `max-drawdown (${(pnlPercent * 100).toFixed(2)}%)`;
    }

    // Check max duration
    if (elapsed >= SPOT_FUTURES_MAX_DURATION_MS) {
      shouldClose = true;
      closeReason = `max-duration (${(elapsed / 1000 / 60).toFixed(1)} min)`;
    }

    if (!shouldClose) continue;

    position.closePending = true;
    const trigger = triggerSource ? ` (trigger=${triggerSource})` : '';
    logInfo(`[SPOT] 🔻 Closing arbitrage ${arbitrageId}: ${closeReason}${trigger}`);
    logInfo(`[SPOT]    Current spread: ${(currentSpread * 100).toFixed(2)}%, PnL: ${totalPnl.toFixed(4)} USDT (${(pnlPercent * 100).toFixed(2)}%)`);

    try {
      await closeSpotFuturesArbitrage(arbitrageId, position);
    } catch (err) {
      position.closePending = false; // allow retry on next book update
      logError(`[SPOT] ❌ Close error for ${arbitrageId}: ${err?.message || err}`);
    }
  }
}

// Monitor and close arbitrage positions
async function monitorSpotFuturesArbitrage() {
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE) return;
  
  for (const [arbitrageId, position] of spotFuturesArbitragePositions) {
    if (position.status !== 'open' || position.closePending) continue;
    
    const { spotSymbol, futuresSymbol, spotQty, futuresVol, spotEntryPrice, futuresEntryPrice, openTime } = position;
    
    // Get current prices
    const spotOb = spotOrderbooks[spotSymbol];
    const futuresOb = orderbooks[futuresSymbol];
    
    if (!spotOb || !spotOb.best_bid) continue;
    if (!futuresOb || !futuresOb.best_sell) continue;
    
    const spotBid = spotOb.best_bid; // Price to sell spot
    const futuresAsk = futuresOb.best_sell; // Price to close short
    
    // Calculate current spread
    const currentSpread = (futuresAsk - spotBid) / spotBid;
    
    // Calculate unrealized PnL
    const spotPnl = (spotBid - spotEntryPrice) * spotQty;
    const futuresPnl = (futuresEntryPrice - futuresAsk) * futuresVol * (contract_sizes[futuresSymbol] || 1);
    const totalPnl = spotPnl + futuresPnl;
    const pnlPercent = totalPnl / (spotEntryPrice * spotQty);
    
    const elapsed = Date.now() - openTime;
    const closeThreshold = elapsed < SPOT_FUTURES_CLOSE_TIME_THRESHOLD_MS
      ? SPOT_FUTURES_CLOSE_THRESHOLD_SHORT
      : SPOT_FUTURES_CLOSE_THRESHOLD_LONG;
    
    let shouldClose = false;
    let closeReason = '';
    
    // Check spread convergence
    if (currentSpread <= closeThreshold) {
      shouldClose = true;
      closeReason = `spread-converged (${(currentSpread * 100).toFixed(2)}% <= ${(closeThreshold * 100).toFixed(2)}%)`;
    }
    
    // Check max drawdown (disabled when <= 0)
    if (SPOT_FUTURES_MAX_DRAWDOWN_PERCENT > 0 && pnlPercent <= -SPOT_FUTURES_MAX_DRAWDOWN_PERCENT) {
      shouldClose = true;
      closeReason = `max-drawdown (${(pnlPercent * 100).toFixed(2)}%)`;
    }
    
    // Check max duration
    if (elapsed >= SPOT_FUTURES_MAX_DURATION_MS) {
      shouldClose = true;
      closeReason = `max-duration (${(elapsed / 1000 / 60).toFixed(1)} min)`;
    }
    
    if (shouldClose) {
      position.closePending = true;
      logInfo(`[SPOT] 🔻 Closing arbitrage ${arbitrageId}: ${closeReason}`);
      logInfo(`[SPOT]    Current spread: ${(currentSpread * 100).toFixed(2)}%, PnL: ${totalPnl.toFixed(4)} USDT (${(pnlPercent * 100).toFixed(2)}%)`);
      
      await closeSpotFuturesArbitrage(arbitrageId, position);
    }
  }
}

// Close arbitrage position
async function closeSpotFuturesArbitrage(arbitrageId, position) {
  const { spotSymbol, futuresSymbol, spotQty, futuresVol, spotEntryPrice, futuresEntryPrice } = position;
  
  logInfo(`[SPOT] Closing arbitrage position ${arbitrageId}...`);
  
  // Step 1: Sell spot
  const spotSellResult = await placeSpotSellOrder(spotSymbol, spotQty);
  
  // Step 2: Close futures short (buy to close)
  const [, volScale] = getSymbolScale(futuresSymbol);
  const futuresCloseOrder = {
    symbol: futuresSymbol,
    side: 2, // Close short = BUY
    openType: SPOT_FUTURES_MARGIN_TYPE,
    type: '5', // Market
    vol: futuresVol,
    leverage: SPOT_FUTURES_LEVERAGE,
    reduceOnly: 'true',
    priceProtect: '0',
    ts: Date.now(),
    marketCeiling: 'false'
  };
  
  const futuresCloseResult = await placeOrder(MEXC_KEY, futuresCloseOrder);
  
  if (spotSellResult || futuresCloseResult) {
    position.status = 'closed';
    position.closeTime = Date.now();
    stats.spotFuturesTradesClosed = (stats.spotFuturesTradesClosed || 0) + 1;
    
    const spotOb = spotOrderbooks[spotSymbol];
    const futuresOb = orderbooks[futuresSymbol];
    const spotExitPrice = spotOb?.best_bid || spotEntryPrice;
    const futuresExitPrice = futuresOb?.best_sell || futuresEntryPrice;
    
    const spotPnl = (spotExitPrice - spotEntryPrice) * spotQty;
    const futuresPnl = (futuresEntryPrice - futuresExitPrice) * futuresVol * (contract_sizes[futuresSymbol] || 1);
    const totalPnl = spotPnl + futuresPnl;
    stats.realizedPnlSpotFutures = (stats.realizedPnlSpotFutures || 0) + totalPnl;
    stats.realizedCountSpotFutures = (stats.realizedCountSpotFutures || 0) + 1;
    
    logInfo(`[SPOT] ✅ Arbitrage ${arbitrageId} closed`);
    logInfo(`[SPOT]    Spot PnL: ${spotPnl.toFixed(4)} USDT, Futures PnL: ${futuresPnl.toFixed(4)} USDT`);
    logInfo(`[SPOT]    Total PnL: ${totalPnl.toFixed(4)} USDT`);
    
    // Calculate PnL percentage (based on initial investment)
    const initialInvestment = spotEntryPrice * spotQty;
    const pnlPercent = initialInvestment > 0 ? (totalPnl / initialInvestment) * 100 : 0;
    
    // Send close notification for spot-futures arbitrage
    sendTradeNotification({
      type: 'close',
      symbol: `${spotSymbol}/${futuresSymbol}`,
      isLong: false, // Always short futures in arbitrage
      pnl: totalPnl,
      pnlPercent: pnlPercent,
      reason: 'arbitrage-closed',
      strategy: 'spot-futures'
    });
    
    // Remove from active positions after a delay
    setTimeout(() => {
      spotFuturesArbitragePositions.delete(arbitrageId);
    }, 5000);
    
    // Refresh balances
    await fetchSpotAccountBalance();
    await refreshBalance('arbitrage-close');
    
    // Send balances after closing
    setTimeout(async () => {
      try {
        await fetchSpotAccountBalance();
        await refreshBalance('arbitrage-close');
        if (balanceReady && Number.isFinite(available_balance)) {
          sendTradeNotification({
            type: 'balance',
            balance: available_balance,
            source: 'futures'
          });
        }
        if (spotBalanceReady && Number.isFinite(spotAvailableBalance)) {
          sendTradeNotification({
            type: 'balance',
            balance: spotAvailableBalance,
            source: 'spot'
          });
        }
      } catch (err) {
        logError(`Failed to send balances after arbitrage close: ${err.message}`);
      }
    }, 2000);

    // Cleanup any remaining spot balance (rounding/partial fills)
    await sellSpotRemainderIfAny(spotSymbol, 'post-close', {
      baseAsset: spotSymbolDetails[spotSymbol]?.baseAsset,
      price: spotExitPrice,
      delayMs: 200
    });
  } else {
    logError(`[SPOT] ❌ Failed to fully close arbitrage ${arbitrageId}`);
    position.closePending = false; // Allow retry
  }
}

// Periodic spot-futures arbitrage monitor
async function runSpotFuturesArbitrageMonitor() {
  if (!ENABLE_SPOT_FUTURES_ARBITRAGE) return;
  
  while (true) {
    try {
      // Scan market data periodically
      await scanSpotMarketData();
    } catch (err) {
      logError(`[SPOT] Monitor error: ${err.message}`);
    }
    
    await sleep(2000); // Market scan loop (close checks are event-driven on orderbook updates)
  }
}

// --- Daily volume helpers (MEXC futures) ------------------------------------------
async function fetchSingleSymbolVolume(symbol, attempt = 1) {
  let delay = VOLUME_RETRY_BASE_DELAY_MS;
  while (attempt <= MAX_VOLUME_FETCH_ATTEMPTS) {
    try {
      const response = await axios.get(`https://contract.mexc.com/api/v1/contract/ticker?symbol=${symbol}`, { timeout: 10000 });
      const data = response.data;
      if (data && data.data) {
        const tickerData = Array.isArray(data.data) ? data.data[0] : data.data;
        if (tickerData && tickerData.symbol) {
          const volume24 = parseFloat(tickerData.turnover24 || tickerData.volume24 || 0);
          if (!Number.isNaN(volume24)) return volume24;
        }
      }
    } catch (_) {
      // silence per mexc_tp.js
    }
    if (attempt < MAX_VOLUME_FETCH_ATTEMPTS) {
      await sleep(delay);
      delay = Math.min(delay * 2, VOLUME_RETRY_MAX_DELAY_MS);
    }
    attempt++;
  }
  return undefined;
}

async function fetchDailyVolumes(symbols, retryMissing = true) {
  const volumes = {};
  const missingSymbols = new Set(symbols);
  const symbolSet = new Set(symbols);

  try {
    logInfo(`[GMGN][Volume] Fetching 24h volumes for ${symbols.length} symbols...`);
    const response = await axios.get('https://contract.mexc.com/api/v1/contract/ticker', { timeout: 15000 });
    const data = response.data;
    if (data && data.data) {
      for (const ticker of data.data) {
        if (ticker.symbol && symbolSet.has(ticker.symbol)) {
          const volume24 = parseFloat(ticker.turnover24 || ticker.volume24 || 0);
          volumes[ticker.symbol] = volume24;
          missingSymbols.delete(ticker.symbol);
        }
      }
    }
  } catch (err) {
    logError(`[GMGN][Volume] Error fetching daily volumes: ${err.message || err}`);
  }

  if (retryMissing && missingSymbols.size > 0) {
    logInfo(`[GMGN][Volume] ${missingSymbols.size} symbols missing volume data. Retrying individually...`);
    const queue = Array.from(missingSymbols);
    const workerCount = 3;
    const updated = new Map();

    const worker = async () => {
      while (queue.length > 0) {
        const symbol = queue.shift();
        if (!symbol) continue;
        const vol = await fetchSingleSymbolVolume(symbol);
        if (vol !== undefined) {
          updated.set(symbol, vol);
          missingSymbols.delete(symbol);
        }
        await sleep(250);
      }
    };

    await Promise.all(Array.from({ length: workerCount }, () => worker()));
    for (const [sym, vol] of updated.entries()) {
      volumes[sym] = vol;
    }
  }

  return { volumes, missingSymbols };
}

async function refreshDailyVolumesPeriodically() {
  if (!ENABLE_GMGN_VOLUME_FILTER) return;
  const REFRESH_INTERVAL_MS = 60 * 60 * 1000; // 1 hour
  while (true) {
    await sleep(REFRESH_INTERVAL_MS);
    try {
      const symbols = gmgnTokenConfigs.map(cfg => cfg.mexc_name);
      logInfo('[GMGN][Volume] Running periodic refresh...');
      await fetchDailyVolumes(symbols, false);
    } catch (err) {
      logWarn(`[GMGN][Volume] Periodic refresh failed: ${err.message || err}`);
    }
  }
}

// --- GMGN URL parsing -------------------------------------------------------------
function extractGmgnInfo(url) {
  const pattern = /https:\/\/gmgn\.ai\/([^/]+)\/token\/([^\/?]+)/;
  const match = String(url || '').match(pattern);
  if (!match) {
    logWarn(`[GMGN] Invalid GMGN URL format: ${url}`);
    return [null, null];
  }
  const network = match[1];
  const rawToken = match[2];
  let token_address = rawToken.split('?')[0].split('_').pop();
  
  // Convert EVM network token addresses to lowercase
  // EVM-compatible networks: eth, bsc, base, arb, polygon, avax, tron, etc.
  const EVM_NETWORKS = new Set(['eth', 'bsc', 'base', 'arb', 'polygon', 'avax', 'tron', 'op', 'zksync', 'linea', 'scroll', 'mantle', 'blast']);
  if (EVM_NETWORKS.has(network.toLowerCase()) && token_address && token_address.startsWith('0x')) {
    token_address = token_address.toLowerCase();
  }
  
  return [network, token_address];
}

// --- GMGN WebSocket (kline) -------------------------------------------------------
async function gmgnWs(network, token) {
  const tokenKey = `${network}:${token}`;
  const FIREFOX_CIPHERS = [
    'TLS_AES_128_GCM_SHA256',
    'TLS_AES_256_GCM_SHA384',
    'TLS_CHACHA20_POLY1305_SHA256',
    'TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256',
    'TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256',
    'TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384',
    'TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384'
  ].join(':');

  const agent = new https.Agent({
    ciphers: FIREFOX_CIPHERS,
    honorCipherOrder: true,
    minVersion: 'TLSv1.2',
    maxVersion: 'TLSv1.3'
  });

  const uri = 'wss://ws.gmgn.ai/quotation';
  let backoff = 5000;
  let lastCloseLogTime = 0;

  while (true) {
    let ws = null;
    let pingInterval = null;

    try {
      ws = new WebSocket(uri, {
        agent,
        headers: {
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:128.0) Gecko/20100101 Firefox/128.0',
          'Sec-WebSocket-Extensions': 'permessage-deflate',
          'Origin': 'https://gmgn.ai',
          'Host': 'ws.gmgn.ai',
          'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
          'Accept-Encoding': 'gzip, deflate, br',
          'Accept-Language': 'en-US,en;q=0.5',
          'Connection': 'keep-alive',
          'Referer': 'https://gmgn.ai/',
          'DNT': '1',
          'Pragma': 'no-cache'
        }
      });

      // Wait for open or error (15s timeout)
      await new Promise((resolve, reject) => {
        const t = setTimeout(() => reject(new Error('GMGN connection timeout')), 15000);
        ws.on('open', () => {
          clearTimeout(t);
          resolve();
        });
        ws.on('error', (err) => {
          clearTimeout(t);
          reject(err);
        });
      });

      backoff = 5000; // reset on successful connect

      const sub1 = {
        action: 'subscribe',
        channel: 'kline',
        id: (crypto.randomUUID ? crypto.randomUUID() : String(Date.now())),
        data: [{ chain: network, addresses: token, interval: '1m' }]
      };
      ws.send(JSON.stringify(sub1));

      if (!gmgnSubscribedTokens.has(tokenKey)) {
        gmgnSubscribedTokens.add(tokenKey);
        gmgnSubscriptionCounter++;
      }
      logInfo(`[GMGN] Subscribed ${network}/${token} (${gmgnSubscriptionCounter}/${gmgnSubscriptions.length})`);

      ws.on('message', (message) => {
        (async () => {
          let rawPayload = '';
          try {
            rawPayload = Buffer.isBuffer(message) ? message.toString('utf8') : String(message);
            const data = JSON.parse(rawPayload);
            if (data.channel === 'kline' && data.data && data.data.length > 0) {
              for (const item of data.data) {
                if (item.n === network && item.a === token) {
                  const price = parseFloat(item.c);
                  const volume = parseFloat(item.v || 0);
                  if (!Number.isFinite(price) || price <= 0) break;
                  gmgnPrices[tokenKey] = price;
                  gmgnVolumes[tokenKey] = volume;

                  const sub = gmgnTokenKeyToSubscription[tokenKey];
                  if (sub) {
                    await checkGmgnSpreadAndTrade(sub.mexc_name, price, volume);
                    monitorGmgnPositionsForClosure(sub.mexc_name, price).catch(err => {
                      logError(`Error in monitorGmgnPositionsForClosure for ${sub.mexc_name}: ${err.message}`);
                    });
                  }
                  break;
                }
              }
            }
          } catch (err) {
            // Keep GMGN WS robust; do not crash on bad payload.
            const now = Date.now();
            const lastTs = gmgnWsParseErrorTs.get(tokenKey) || 0;
            if ((now - lastTs) >= 30000) {
              gmgnWsParseErrorTs.set(tokenKey, now);
              const preview = rawPayload
                ? (rawPayload.length > 240 ? `${rawPayload.slice(0, 240)}...` : rawPayload)
                : '<empty payload>';
              logWarn(`[GMGN] WS parse error for ${network}/${token}: ${err.message || err}. Payload: ${preview}`);
            }
          }
        })();
      });

      ws.on('error', (err) => {
        // Suppress noisy 429 logs; reconnect loop will handle backoff.
        const s = String(err || '');
        if (!s.includes('429') && !s.includes('Unexpected server response: 429')) {
          logWarn(`[GMGN] WS error for ${network}/${token}: ${s}`);
        }
        try {
          if (ws && ws.readyState !== WebSocket.CLOSED && ws.readyState !== WebSocket.CLOSING) {
            ws.close();
          }
        } catch (_) {}
      });

      ws.on('close', () => {
        const now = Date.now();
        if (now - lastCloseLogTime > 30000) {
          logWarn(`[GMGN] WS closed for ${network}/${token}`);
          lastCloseLogTime = now;
        }
      });

      pingInterval = setInterval(() => {
        try {
          if (ws && ws.readyState === WebSocket.OPEN) {
            ws.send(JSON.stringify({ action: 'ping' }));
          }
        } catch (_) {}
      }, 10000);

      await new Promise((resolve) => ws.on('close', resolve));
    } catch (err) {
      const s = String(err?.message || err || '');
      if (!s.includes('429') && !s.includes('Unexpected server response: 429')) {
        logWarn(`[GMGN] Connect loop error for ${network}/${token}: ${s}`);
      }
    } finally {
      if (pingInterval) clearInterval(pingInterval);
      try { if (ws) ws.terminate(); } catch (_) {}
    }

    await sleep(backoff);
    backoff = Math.min(backoff * 2, 60000);
  }
}

// --- GMGN subscription setup/start ------------------------------------------------
async function setupGmgnSubscriptions() {
  if (!ENABLE_GMGN_SPREAD_TRADING) return [];

  gmgnTokenConfigs = loadGmgnTokenConfigsFromFile();
  gmgnSubscriptions = [];
  gmgnConfigBySymbol.clear();
  for (const k of Object.keys(gmgnTokenKeyToSubscription)) delete gmgnTokenKeyToSubscription[k];
  for (const k of Object.keys(gmgnSymbolToTokenKey)) delete gmgnSymbolToTokenKey[k];

  if (!gmgnTokenConfigs || gmgnTokenConfigs.length === 0) {
    logWarn('[GMGN] No token configs available - skipping GMGN subscriptions');
    return [];
  }

  const allSymbols = gmgnTokenConfigs.map(cfg => cfg.mexc_name);

  if (ENABLE_DEPOSIT_WITHDRAW_CHECK) {
    logInfo('[GMGN] Checking deposit/withdraw status for GMGN tokens...');
    await buildDepositWithdrawBlacklist(allSymbols, true);
  }

  let dailyVolumes = {};
  if (ENABLE_GMGN_VOLUME_FILTER) {
    const { volumes } = await fetchDailyVolumes(allSymbols, false);
    dailyVolumes = volumes || {};
  }

  const filteredOut = [];
  const kept = [];

  for (const tokenCfg of gmgnTokenConfigs) {
    if (isTickerBlacklisted(tokenCfg.mexc_name)) {
      filteredOut.push({ symbol: tokenCfg.mexc_name, reason: 'Blacklisted ticker' });
      continue;
    }
    if (ENABLE_DEPOSIT_WITHDRAW_CHECK && isDepositWithdrawBlacklisted(tokenCfg.mexc_name)) {
      filteredOut.push({ symbol: tokenCfg.mexc_name, reason: 'Deposit/Withdrawal disabled' });
      continue;
    }
    if (!tokenCfg.gmgn_url) {
      filteredOut.push({ symbol: tokenCfg.mexc_name, reason: 'No GMGN URL' });
      continue;
    }

    const [network, token_address] = extractGmgnInfo(tokenCfg.gmgn_url);
    if (!network || !token_address) {
      filteredOut.push({ symbol: tokenCfg.mexc_name, reason: 'Invalid GMGN URL' });
      continue;
    }

    if (ENABLE_GMGN_VOLUME_FILTER) {
      const dailyVolume = dailyVolumes[tokenCfg.mexc_name];
      if (dailyVolume !== undefined && Number.isFinite(dailyVolume) && dailyVolume < MIN_DAILY_VOLUME_USD) {
        filteredOut.push({
          symbol: tokenCfg.mexc_name,
          reason: `Daily volume ${Number(dailyVolume).toFixed(2)} < ${MIN_DAILY_VOLUME_USD}`
        });
        continue;
      }
    }

    const baseName = tokenCfg.mexc_name.endsWith('_USDT')
      ? tokenCfg.mexc_name.slice(0, -5)
      : tokenCfg.mexc_name;

    let openThreshold;
    if (Object.prototype.hasOwnProperty.call(SPECIAL_OPEN_THRESHOLDS, baseName)) {
      openThreshold = SPECIAL_OPEN_THRESHOLDS[baseName];
    } else if (OPEN_THRESHOLD_EXCEPTIONS.has(baseName)) {
      openThreshold = Number(tokenCfg.percentagecountforopen) || DEFAULT_OPEN_THRESHOLD;
    } else {
      openThreshold = DEFAULT_OPEN_THRESHOLD;
    }
    tokenCfg.percentagecountforopen = openThreshold;

    const tokenKey = `${network}:${token_address}`;
    const sub = {
      network,
      tokenContractAddress: token_address,
      tokenKey,
      mexc_name: tokenCfg.mexc_name,
      displayName: baseName,
      margin_percent: Number(tokenCfg.margin_percent ?? GMGN_DEFAULT_MARGIN_PERCENT),
      leverage: Number(tokenCfg.leverage ?? GMGN_DEFAULT_LEVERAGE),
      percentagecountforopen: openThreshold,
      normalDifferencePercent: Number(tokenCfg.normalDifferencePercent ?? 1),
      normalSpreadClosure: Number(tokenCfg.normalSpreadClosure ?? 1),
      maxDrawdown: Number(tokenCfg.maxDrawdown ?? 8)
    };

    gmgnSubscriptions.push(sub);
    gmgnTokenKeyToSubscription[tokenKey] = sub;
    gmgnSymbolToTokenKey[tokenCfg.mexc_name] = tokenKey;
    gmgnConfigBySymbol.set(tokenCfg.mexc_name, tokenCfg);

    // Ensure orderbook structures exist (they will be populated by WS orderbook updaters)
    if (!orderbooks[tokenCfg.mexc_name]) {
      orderbooks[tokenCfg.mexc_name] = {
        buy_orders: [],
        sell_orders: [],
        best_buy: null,
        best_sell: null,
        depthTs: null,
        _counted: false
      };
    }
    if (lastOrderTime[tokenCfg.mexc_name] === undefined) {
      lastOrderTime[tokenCfg.mexc_name] = 0;
    }

    kept.push({ symbol: tokenCfg.mexc_name });
  }

  logInfo(`[GMGN] Startup report: loaded=${gmgnTokenConfigs.length}, kept=${kept.length}, filtered=${filteredOut.length}`);
  if (filteredOut.length > 0) {
    const reasonCounts = new Map();
    for (const item of filteredOut) {
      reasonCounts.set(item.reason, (reasonCounts.get(item.reason) || 0) + 1);
    }
    const reasonSummary = Array.from(reasonCounts.entries())
      .sort((a, b) => b[1] - a[1])
      .map(([reason, count]) => `${reason}=${count}`)
      .join(', ');
    if (reasonSummary) {
      logInfo(`[GMGN] Filter reasons: ${reasonSummary}`);
    }
    const sample = filteredOut.slice(0, 10);
    logInfo(`[GMGN] Filtered sample (up to 10): ${sample.map(x => `${x.symbol}(${x.reason})`).join(', ')}`);
  }

  let startedOrderbooks = 0;
  for (const sub of gmgnSubscriptions) {
    if (ensureOrderbookUpdaterStarted(sub.mexc_name, 'gmgn-setup')) {
      startedOrderbooks++;
    }
  }
  if (gmgnSubscriptions.length > 0) {
    logInfo(`[GMGN] Orderbook updaters ensured: total=${gmgnSubscriptions.length}, startedNow=${startedOrderbooks}, alreadyRunning=${Math.max(0, gmgnSubscriptions.length - startedOrderbooks)}`);
  }

  return gmgnSubscriptions;
}

async function startGmgnWebsockets() {
  if (!ENABLE_GMGN_SPREAD_TRADING) return;
  if (!gmgnSubscriptions || gmgnSubscriptions.length === 0) {
    logWarn('[GMGN] No subscriptions - not starting GMGN websockets');
    return;
  }

  gmgnSubscriptionCounter = 0;
  gmgnSubscribedTokens.clear();

  for (let i = 0; i < gmgnSubscriptions.length; i++) {
    const sub = gmgnSubscriptions[i];
    gmgnWs(sub.network, sub.tokenContractAddress);
    if (i < gmgnSubscriptions.length - 1) {
      const jitter = GMGN_WS_CONNECT_DELAY_MIN_MS + Math.random() * (GMGN_WS_CONNECT_DELAY_MAX_MS - GMGN_WS_CONNECT_DELAY_MIN_MS);
      await sleep(jitter);
    }
  }
}

async function fetchOrderbookDeepRest(symbol, depth) {
  const url = `https://contract.mexc.com/api/v1/contract/depth/${symbol}?limit=${depth}`;
  const resp = await axios.get(url, { timeout: 10000 });
  // API returns bids/asks as [price, size]
  if (!resp.data || !resp.data.data) return null;
  const { bids = [], asks = [] } = resp.data.data;
  const buy_orders = bids.map(([p, q]) => [Number(p), Number(q)]).filter(([p, q]) => p > 0 && q > 0);
  const sell_orders = asks.map(([p, q]) => [Number(p), Number(q)]).filter(([p, q]) => p > 0 && q > 0);
  if (!buy_orders.length || !sell_orders.length) return null;
  return {
    buy_orders: buy_orders.sort((a, b) => b[0] - a[0]),
    sell_orders: sell_orders.sort((a, b) => a[0] - b[0]),
    best_buy: buy_orders[0][0],
    best_sell: sell_orders[0][0],
    depthTs: Date.now()
  };
}

async function scanOrderbooksForSlippage() {
  const now = Date.now();
  let updatedWs = 0;
  let constrained = 0;
  const restQueue = [];

  // Pass 1: try WS (existing depth)
  for (const [symbol, ob] of Object.entries(orderbooks)) {
    if (BLACKLISTED_SYMBOLS.has(symbol)) continue;
    if (!symbolIsUSDT[symbol]) continue;
    if (!isOrderbookFresh(ob, now)) {
      restQueue.push(symbol);
      continue;
    }

    const contractSize = contract_sizes[symbol] || 1;
    let applied = false;
    const depthLimit = Math.max(1, Math.min(ORDERBOOK_DEPTH, OB_SCAN_DEPTH_LEVELS || ORDERBOOK_DEPTH));
    const depthStats = computeDepthSlippageAtLimit(ob, depthLimit, contractSize);
    const maxBps = MAX_SLIPPAGE_BPS / 10000;
    if (depthStats && depthStats.worst > 0 && depthStats.slipAsk <= maxBps && depthStats.slipBid <= maxBps && depthStats.worst >= SLIPPAGE_TEST_NOTIONAL) {
      const prev = maxPositionNotional.get(symbol);
      if (!prev || prev.worst > depthStats.worst) constrained++;
      const changed = !prev
        || prev.worst !== depthStats.worst
        || prev.longNotional !== depthStats.longNotional
        || prev.shortNotional !== depthStats.shortNotional;
      if (changed) {
        maxPositionNotional.set(symbol, { ...depthStats, ts: now, source: 'ws-depth' });
        updatedWs++;
      }
      applied = true;
    }

    if (!applied) {
      const res = computeMaxNotionalBySlippage(ob, MAX_SLIPPAGE_BPS, contractSize);
      // If WS calc doesn't yield enough notional, push to REST
      if (!res || !res.worst || res.worst < SLIPPAGE_TEST_NOTIONAL) {
        restQueue.push(symbol);
        continue;
      }
      const prev = maxPositionNotional.get(symbol);
      if (!prev || prev.worst > res.worst) constrained++;
      const changed = !prev
        || prev.worst !== res.worst
        || prev.longNotional !== res.longNotional
        || prev.shortNotional !== res.shortNotional;
      if (changed) {
        maxPositionNotional.set(symbol, { ...res, ts: now, source: 'ws' });
        updatedWs++;
      }
    }
  }

  let updatedRest = 0;
  let failedRest = 0;

  // Pass 2: REST deep scan for missing symbols, rate limited
  if (OB_REST_SCAN_INTERVAL_MS > 0 && OB_REST_DEPTH > 0 && restQueue.length) {
    for (const symbol of restQueue) {
      const lastTs = lastRestScanTs.get(symbol) || 0;
      if ((now - lastTs) < OB_REST_SCAN_INTERVAL_MS) continue; // too recent
      try {
        const obDeep = await fetchOrderbookDeepRest(symbol, OB_REST_DEPTH);
        lastRestScanTs.set(symbol, Date.now());
        if (!obDeep) {
          failedRest++;
          await sleep(OB_REST_PAUSE_MS);
          continue;
        }
        const contractSize = contract_sizes[symbol] || 1;
        const res = computeMaxNotionalBySlippage(obDeep, MAX_SLIPPAGE_BPS, contractSize);
        if (!res) {
          failedRest++;
          await sleep(OB_REST_PAUSE_MS);
          continue;
        }
        const prev = maxPositionNotional.get(symbol);
        if (!prev || prev.worst > res.worst) constrained++;
        const changed = !prev
          || prev.worst !== res.worst
          || prev.longNotional !== res.longNotional
          || prev.shortNotional !== res.shortNotional;
        if (changed) {
          maxPositionNotional.set(symbol, { ...res, ts: Date.now(), source: 'rest' });
          updatedRest++;
        }
        await sleep(OB_REST_PAUSE_MS);
      } catch (err) {
        failedRest++;
        lastRestScanTs.set(symbol, Date.now());
        await sleep(OB_REST_PAUSE_MS);
        continue;
      }
    }
  }

  if (updatedWs > 0 || updatedRest > 0) {
    const constrainedMsg = constrained > 0 ? `, constrained=${constrained}` : '';
    logInfo(`🔎 Slippage scan updated (ws=${updatedWs}, rest=${updatedRest}, failRest=${failedRest}) max ${MAX_SLIPPAGE_BPS} bps${constrainedMsg}`);
  }
}

function getActiveTrade(symbol) {
  return activeTrades.get(symbol);
}

function registerActiveTrade(symbol, payload) {
  const tradeState = {
    symbol,
    strategy: payload.strategy || 'fair',
    direction: payload.direction,
    isLong: payload.isLong,
    entryPrice: payload.entryPrice,
    entryTime: Date.now(),
    leverage: payload.leverage,
    openType: payload.openType || (payload.strategy === 'gmgn' ? 2 : 1), // GMGN: cross (2), FAIR: isolated (1)
    openVol: payload.volume,
    remainingVol: payload.volume,
    initialSpread: payload.initialSpread,
    referencePrice: payload.referencePrice || null, // optional (e.g., GMGN price snapshot)
    stopLossPrice: payload.stopLossPrice || null,
    positionId: null,
    partialCloseRequested: false,
    pendingCloseVol: 0,
    pendingCloseReason: null,
    lastCloseAttempt: null,
    closeRetries: 0,
    lastKnownVol: payload.volume,
    killSwitchTriggered: false,
    tpOrdersPlaced: payload.tpOrdersPlaced !== undefined ? payload.tpOrdersPlaced : false // For GMGN (skipTpLimitPlacement=true), TP will be placed in handlePositionUpdate, so keep false initially
  };
  activeTrades.set(symbol, tradeState);
  logInfo(`   🧠 Tracking trade for ${symbol} [${tradeState.strategy}] (${payload.direction}) | entry ${payload.entryPrice.toFixed(8)}, vol=${payload.volume}`);
  return tradeState;
}

function finalizeActiveTrade(symbol, reason = 'completed') {
  const trade = activeTrades.get(symbol);
  if (trade) {
    logInfo(`   ✅ Trade lifecycle finished for ${symbol} (${trade.direction}) due to ${reason}`);
    activeTrades.delete(symbol);
  }
}

function flagManualHoldIfLive(symbol) {
  const posMap = symbolPositions.get(symbol);
  const hasLivePos = posMap && [...posMap.values()].some(p => p.holdVol > 0 && !closed_positions.has(p.positionId || ""));
  if (hasLivePos) {
    manualPositionHold.add(symbol);
    logWarn(`🚫 ${symbol}: detected existing open position, skipping this symbol until position is closed.`);
    return true;
  }
  return false;
}

async function ensureManualHoldIfLive(symbol, retryDelayMs = 800) {
  if (flagManualHoldIfLive(symbol)) return true;
  if (retryDelayMs > 0) {
    await sleep(retryDelayMs);
    if (flagManualHoldIfLive(symbol)) return true;
  }
  return false;
}

function computeExitPrice(trade, ob, lastPrice) {
  if (!trade) return null;
  if (trade.isLong) {
    return (ob && ob.best_buy) || (lastPrice > 0 ? lastPrice : null) || trade.entryPrice;
  }
  return (ob && ob.best_sell) || (lastPrice > 0 ? lastPrice : null) || trade.entryPrice;
}

function computePnlPercent(trade, exitPrice) {
  if (!trade || !exitPrice) return 0;
  if (trade.isLong) {
    return (exitPrice - trade.entryPrice) / trade.entryPrice;
  }
  return (trade.entryPrice - exitPrice) / trade.entryPrice;
}

function computeUnrealizedPnlUSDT(trade, exitPrice) {
  if (!trade || !Number.isFinite(exitPrice) || exitPrice <= 0) return null;
  const vol = Number(trade.remainingVol ?? trade.openVol);
  if (!Number.isFinite(vol) || vol <= 0) return null;
  const cs = contract_sizes[trade.symbol] || 1;
  if (!Number.isFinite(cs) || cs <= 0) return null;
  return trade.isLong
    ? (exitPrice - trade.entryPrice) * vol * cs
    : (trade.entryPrice - exitPrice) * vol * cs;
}

async function requestClosePosition(symbol, trade, closeVol, reason, force = false) {
  if (!trade) return;
  if (!trade.positionId && trade.remainingVol <= 0) return; // nothing to close
  const [ , volScale ] = getSymbolScale(symbol);
  let volume = adjustVol(closeVol, volScale);
  if (volume <= 0) {
    return;
  }
  volume = Math.min(volume, trade.remainingVol || volume);

  if (volume <= 0) return;

  const now = Date.now();
  if (!force && trade.pendingCloseVol > 0 && trade.lastCloseAttempt && (now - trade.lastCloseAttempt) < CLOSE_RETRY_INTERVAL_MS) {
    return; // avoid spamming close orders
  }

  const side = trade.isLong ? 4 : 2; // Close long -> 4, close short -> 2
  const order = {
    symbol,
    side,
    openType: trade.openType || (trade.strategy === 'gmgn' ? 2 : 1), // GMGN: cross (2), FAIR: isolated (1)
    type: "5",
    vol: volume,
    leverage: trade.leverage || getMaxLeverage(symbol),
    reduceOnly: "true",
    priceProtect: "0",
    ts: Date.now(),
    marketCeiling: 'false'
  };

  logInfo(`   🔻 Reduce-only close request for ${symbol} (${reason}) vol=${volume}`);
  const resp = await placeOrder(MEXC_KEY, order);
  if (resp && resp.success) {
    trade.pendingCloseVol = volume;
    trade.pendingCloseReason = reason;
    trade.lastCloseAttempt = now;
    trade.closeRetries = 0;
    logInfo(`   📤 Submitted close order for ${symbol} (${reason})`);
  } else {
    logError(`❌ Failed to submit close order for ${symbol} (${reason}): ${JSON.stringify(resp)}`);
    // Even on error, keep pendingCloseVol if spread is converged (will retry)
    // This ensures we continue trying to close until position is closed or spread becomes workable
    if (reason.includes('spread-converged') || reason.includes('partial-spread') || reason.includes('retry')) {
      trade.pendingCloseVol = volume;
      trade.pendingCloseReason = reason;
      trade.lastCloseAttempt = now;
    }
  }
  return resp;
}

// Place three reduce-only limit TP orders (25% of volume each) at +/-2%, +/-3%, +/-4% from entry price
// Note: Each TP order takes ~25% of position volume, leaving ~25% as "runner" for potential higher profits
async function placeTakeProfitLimits(symbol, tradeContext) {
  const { isLong, volume, entryPrice, leverage } = tradeContext;
  const openType = tradeContext.openType || (tradeContext.strategy === 'gmgn' ? 2 : 1); // GMGN: cross (2), FAIR: isolated (1)
  if (!entryPrice || !volume || volume <= 0) return;
  const [priceScale, volScale] = getSymbolScale(symbol);
  const sideClose = isLong ? 4 : 2; // close long -> sell, close short -> buy
  const minVolumeStep = volScale === 0 ? 1 : Math.pow(10, -volScale);

  // TP sizing strategy:
  // - Allocate ~25% of total volume to each TP (TP1/2/3), leaving the remainder as a "runner"
  // - For small positions (e.g. volume=1 with volScale=0), ensure we still place at least one TP if possible
  // - Never exceed total volume, respect lot-size via adjustVol()
  const totalVol = volume;
  let remaining = totalVol;
  const desiredRaws = [0.25, 0.25, 0.25].map(r => totalVol * r);
  const tpVols = [];
  for (const raw of desiredRaws) {
    let v = adjustVol(raw, volScale);
    if (v < minVolumeStep && remaining >= minVolumeStep) {
      v = minVolumeStep;
    }
    v = Math.min(v, remaining);
    if (v <= 0) v = 0;
    tpVols.push(v);
    remaining -= v;
  }

  const tp1Price = isLong
    ? roundToScale(entryPrice * (1 + TP_LIMIT_1_PCT), priceScale)
    : roundToScale(entryPrice * (1 - TP_LIMIT_1_PCT), priceScale);
  const tp2Price = isLong
    ? roundToScale(entryPrice * (1 + TP_LIMIT_2_PCT), priceScale)
    : roundToScale(entryPrice * (1 - TP_LIMIT_2_PCT), priceScale);
  const tp3Price = isLong
    ? roundToScale(entryPrice * (1 + TP_LIMIT_3_PCT), priceScale)
    : roundToScale(entryPrice * (1 - TP_LIMIT_3_PCT), priceScale);

  const prices = [tp1Price, tp2Price, tp3Price];
  const pctLabels = [TP_LIMIT_1_PCT, TP_LIMIT_2_PCT, TP_LIMIT_3_PCT];
  
  // Safety check: Verify TP prices are in correct direction (LONG: TP > entry, SHORT: TP < entry)
  for (let i = 0; i < prices.length; i++) {
    const isValid = isLong ? prices[i] > entryPrice : prices[i] < entryPrice;
    if (!isValid) {
      logError(`❌ ${symbol}: Invalid TP${i + 1} price ${prices[i]} for ${isLong ? 'LONG' : 'SHORT'} position (entry: ${entryPrice}). Skipping TP placement.`);
      return;
    }
  }
  
  // Log TP volume distribution for verification
  const totalTpVol = tpVols.reduce((sum, v) => sum + v, 0);
  logInfo(`   📊 ${symbol}: TP volume distribution - TP1: ${tpVols[0]}, TP2: ${tpVols[1]}, TP3: ${tpVols[2]}, Total: ${totalTpVol}/${totalVol} (${((totalTpVol / totalVol) * 100).toFixed(1)}%)`);

  for (let i = 0; i < prices.length; i++) {
    let vol = tpVols[i] || 0;
    if (vol < minVolumeStep) {
      logWarn(`   ⚠️ ${symbol}: TP limit vol ${vol} below min step ${minVolumeStep}, skipping TP ${i + 1}`);
      continue;
    }
    // Delay between TP orders: TP1=800ms, TP2=1200ms, TP3=1600ms
    const tpDelays = [800, 1200, 1600];
    await sleep(tpDelays[i] || 800);

    // Delays between attempts within one TP: 200ms, 400ms, 800ms, 1200ms, 1800ms, 2400ms
    const attemptDelays = [200, 400, 800, 1200, 1800, 2400];
    let attempt = 0;
    const maxAttempts = 6; // Increased to 6 attempts
    let placed = false;

    while (attempt < maxAttempts && !placed) {
      attempt++;
      const order = {
        symbol,
        side: sideClose,
        openType, // match position margin mode
        type: "1", // Limit
        price: prices[i],
        vol,
        leverage: leverage || getMaxLeverage(symbol),
        reduceOnly: "true",
        priceProtect: "0",
        ts: Date.now(),
        marketCeiling: 'false'
      };
      const pct = pctLabels[i] * 100;
      logInfo(`   🎯 Placing TP${i + 1} limit for ${symbol} vol=${vol} price=${prices[i]} (${(isLong ? '+' : '-')} ${pct}% from entry) attempt ${attempt}/${maxAttempts}`);
      const resp = await placeOrder(MEXC_KEY, order);
      if (resp && resp.success) {
        logInfo(`   ✅ TP${i + 1} limit placed for ${symbol}: ${JSON.stringify(resp)}`);
        placed = true;
      } else {
        const isRateLimitError = resp && resp.code === 510;
        logWarn(`   ⚠️ Failed to place TP${i + 1} limit for ${symbol}: ${JSON.stringify(resp)}`);
        
        if (isRateLimitError && attempt >= maxAttempts) {
          // Schedule retry for rate limit errors after all attempts exhausted
          // Minimal delay: 2 seconds - enough to avoid rate limit but keep bot responsive
          const retryAfter = 2000; // Retry after 2 seconds (minimal delay to avoid rate limits)
          if (!pendingTPRetries.has(symbol)) {
            pendingTPRetries.set(symbol, []);
          }
          const retryList = pendingTPRetries.get(symbol);
          // Check if this TP is already in retry list
          const existingRetry = retryList.find(r => r.tpIndex === i + 1);
          if (!existingRetry) {
            retryList.push({
              tpIndex: i + 1,
              price: prices[i],
              vol,
              isLong,
              leverage: leverage || getMaxLeverage(symbol),
              retryAfter: Date.now() + retryAfter,
              retryCount: 0,
              maxRetries: 6, // Maximum 6 retry attempts
              pct: pct
            });
            logInfo(`   ⏳ Scheduled retry for TP${i + 1} on ${symbol} after ${retryAfter/1000}s (rate limit error 510)`);
          } else {
            logInfo(`   ⏳ TP${i + 1} for ${symbol} already in retry queue, skipping duplicate`);
          }
        }
        
        // Apply delay after each failed attempt (including the last one)
        // This helps avoid rate limits even after the final attempt
        const delay = attemptDelays[attempt - 1] || 2400; // Use predefined delay or max (2400ms for attempt 6)
        if (attempt < maxAttempts) {
          await sleep(delay);
        } else {
          // Even after the last attempt, wait 2400ms to avoid rate limits before moving to next TP
          await sleep(delay);
        }
      }
    }
  }
}

// Place Take Profit limit order for GMGN strategy (from spread.js)
async function placeTakeProfitLimitOrder(symbol, pos, takeProfitPercent = 5) {
  try {
    const position_id = pos.positionId;
    
    // Check if position is still open before placing TP order
    if (closed_positions.has(String(position_id))) {
      logInfo(`Position ${position_id} on ${symbol} already closed, skipping TP order placement.`);
      return false;
    }
    
    // Get fresh position data to check if still open
    const currentPos = positions[String(position_id)];
    if (!currentPos || currentPos.state === 3 || !currentPos.holdVol || currentPos.holdVol <= 0) {
      logInfo(`Position ${position_id} on ${symbol} is closed or has zero volume, skipping TP order placement.`);
      return false;
    }
    
    const hold_vol = currentPos.holdVol || 0;
    
    if (!hold_vol || hold_vol <= 0) {
      logWarn(`Cannot place TP order for position ${position_id} on ${symbol}: zero holdVol`);
      return false;
    }

    // Get position opening price from MEXC (use current position data)
    const openPrice = currentPos.openAvgPrice || currentPos.openPrice || pos.openAvgPrice || pos.openPrice;
    if (!openPrice) {
      logWarn(`Cannot place TP order for position ${position_id} on ${symbol}: no openPrice`);
      return false;
    }

    const isLong = currentPos.positionType === 1;
    const leverage = pos.leverage || 20;
    
    // Get openType from position or active trade (GMGN uses cross=2)
    const trade = getActiveTrade(symbol);
    const openType = pos.openType || currentPos.openType || (trade?.openType) || (trade?.strategy === 'gmgn' ? 2 : 1);
    
    const [priceScale, volScale] = getSymbolScale(symbol);
    const baseTpPercent = takeProfitPercent;

    const tpOrders = [{ percent: baseTpPercent, volume: hold_vol }];
    const recordedTpOrderIds = [];

    const submitTpOrder = async (tpPercent, volume) => {
      const side = isLong ? 4 : 2;
      let attempts = 0;
      while (attempts < 2) {
        attempts++;
        let tpPrice = isLong
          ? openPrice * (1 + tpPercent / 100)
          : openPrice * (1 - tpPercent / 100);
        tpPrice = roundToScale(tpPrice, priceScale);

        const order = {
          symbol,
          side,
          openType: openType, // Use openType from position/trade (GMGN: cross=2, FAIR: isolated=1)
          type: "1",
          vol: volume,
          price: String(tpPrice),
          leverage,
          positionId: position_id,
          priceProtect: "0",
          ts: Date.now(),
          marketCeiling: 'false'
        };

        const resp = await placeOrder(MEXC_KEY, order);
        logInfo(`\n🎯 Placing Take Profit limit order for position ${position_id} on ${symbol}:`);
        logInfo(`   Position: ${isLong ? 'LONG' : 'SHORT'}, Open Price: ${openPrice.toFixed(8)}`);
        logInfo(`   TP: ${tpPercent}%, TP Price: ${tpPrice.toFixed(8)}, Volume: ${volume}`);
        logInfo(`Take Profit order response: ${JSON.stringify(resp)}`);

        if (resp && resp.success) {
          let tpOrderId = null;
          try {
            if (resp.data && typeof resp.data === "object") {
              tpOrderId = String(resp.data.orderId);
            } else if (resp.orderId) {
              tpOrderId = String(resp.orderId);
            }
          } catch (e) {
            tpOrderId = null;
          }
          if (tpOrderId) {
            recordedTpOrderIds.push(tpOrderId);
          }
          return;
        }

        if (resp && resp.code === 510 && attempts < 2) {
          logWarn(`⚠️ Rate limit error (510) for TP order ${tpPercent}% on position ${position_id}. Retrying in 2s...`);
          await new Promise(resolve => setTimeout(resolve, 2000));
          const stillOpen = positions[String(position_id)];
          if (!stillOpen || stillOpen.state === 3 || closed_positions.has(String(position_id))) {
            logInfo(`Position ${position_id} closed before TP retry could be attempted.`);
            return;
          }
          continue;
        } else {
          logWarn(`❌ Failed to place TP order ${tpPercent}% for position ${position_id}: ${JSON.stringify(resp)}`);
          return;
        }
      }
    };

    for (const tpCfg of tpOrders) {
      if (!tpCfg.volume || tpCfg.volume <= 0) continue;
      await submitTpOrder(tpCfg.percent, tpCfg.volume);
    }

    if (recordedTpOrderIds.length > 0) {
      positionTpOrders[position_id] = recordedTpOrderIds;
      return true;
    }

    return false;
  } catch (err) {
    logError(`Error placing Take Profit order for position ${pos.positionId} on ${symbol}: ${err.message || err}`);
    return false;
  }
}

// Retry pending TP orders that failed due to rate limiting (code 510)
async function retryPendingTPOrders() {
  const now = Date.now();
  const retryDelayMs = 500;
  const symbolsToRetry = Array.from(pendingTPRetries.keys());
  
  for (const symbol of symbolsToRetry) {
    const retryList = pendingTPRetries.get(symbol);
    if (!retryList || retryList.length === 0) {
      pendingTPRetries.delete(symbol);
      continue;
    }
    
    // Check if position still exists
    const trade = getActiveTrade(symbol);
    if (!trade || (trade.positionId && closed_positions.has(String(trade.positionId)))) {
      // Position closed, remove pending retries
      pendingTPRetries.delete(symbol);
      continue;
    }
    
    // Process retries that are ready
    const remainingRetries = [];
    for (const retry of retryList) {
      if (now >= retry.retryAfter) {
        // Time to retry
        if (retry.retryCount >= retry.maxRetries) {
          logWarn(`   ⚠️ ${symbol}: TP${retry.tpIndex} retry limit reached (${retry.maxRetries} attempts), giving up`);
          continue; // Skip this retry, don't add to remaining
        }

        if (typeof trade.isLong === 'boolean' && trade.isLong !== retry.isLong) {
          logWarn(`   ⚠️ ${symbol}: TP${retry.tpIndex} direction mismatch, skipping retry`);
          continue;
        }
        
        retry.retryCount++;
        const sideClose = retry.isLong ? 4 : 2;
        const openType = trade.openType || (trade.strategy === 'gmgn' ? 1 : 2); // GMGN: cross (1), FAIR: isolated (2)
        
        const order = {
          symbol,
          side: sideClose,
          openType, // match position margin mode
          type: "1", // Limit
          price: retry.price,
          vol: retry.vol,
          leverage: retry.leverage,
          reduceOnly: "true",
          priceProtect: "0",
          ts: Date.now(),
          marketCeiling: 'false'
        };
        
        logInfo(`   🔄 Retrying TP${retry.tpIndex} for ${symbol} (attempt ${retry.retryCount}/${retry.maxRetries})`);
        const resp = await placeOrder(MEXC_KEY, order);
        
        if (resp && resp.success) {
          logInfo(`   ✅ TP${retry.tpIndex} limit placed successfully on retry for ${symbol}: ${JSON.stringify(resp)}`);
          // Success, don't add to remaining
        } else if (resp && resp.code === 2009) {
          // Position closed
          logWarn(`   ⚠️ ${symbol}: TP${retry.tpIndex} failed because position is closed, stopping retries`);
        } else if (retry.retryCount >= retry.maxRetries) {
          logError(`   ❌ ${symbol}: TP${retry.tpIndex} failed after ${retry.maxRetries} retry attempts: ${JSON.stringify(resp)}`);
        } else {
          retry.retryAfter = Date.now() + retryDelayMs;
          remainingRetries.push(retry);
          logWarn(`   ⚠️ ${symbol}: TP${retry.tpIndex} failed, retrying in ${retryDelayMs}ms (attempt ${retry.retryCount}/${retry.maxRetries}): ${JSON.stringify(resp)}`);
        }
      } else {
        // Not ready yet, keep for later
        remainingRetries.push(retry);
      }
    }
    
    if (remainingRetries.length > 0) {
      pendingTPRetries.set(symbol, remainingRetries);
    } else {
      pendingTPRetries.delete(symbol);
    }
  }
}

// Close helper that respects maxVol for open positions and chunks by 90% of maxVol with 100ms delay
async function closeWithMaxVol(symbol, trade, desiredCloseVol, reason) {
  const [, volScale, maxVol] = getSymbolScale(symbol);
  const minVolumeStep = volScale === 0 ? 1 : Math.pow(10, -volScale);
  const chunkDelayMs = 100;
  let effectiveMaxVol = maxVol;

  // If maxVol is zero/invalid, attempt full close once; if error returns allowed amount, use it
  if (effectiveMaxVol === null || effectiveMaxVol === undefined || effectiveMaxVol <= 0) {
    const resp = await requestClosePosition(symbol, trade, desiredCloseVol, reason, false);
    if (resp && !resp.success && resp._extend && Number(resp._extend.amount) > 0) {
      effectiveMaxVol = Number(resp._extend.amount);
      logWarn(`   ⚠️ ${symbol}: maxVol=0 on close, using allowed close cap from error: ${effectiveMaxVol}`);
    } else {
      return;
    }
  }

  const chunkSizeRaw = effectiveMaxVol * 0.9;
  const chunkSize = adjustVol(chunkSizeRaw, volScale);
  if (chunkSize <= 0 || chunkSize < minVolumeStep) {
    logWarn(`   ⚠️ ${symbol}: Computed chunk ${chunkSize} below min step ${minVolumeStep}, attempting full close of desired volume.`);
    await requestClosePosition(symbol, trade, desiredCloseVol, reason, false);
    return;
  }

  let remainingToClose = Math.min(desiredCloseVol, trade.remainingVol || desiredCloseVol);

  while (remainingToClose > 0 && trade.remainingVol > 0) {
    const vol = Math.min(remainingToClose, chunkSize);
    await requestClosePosition(symbol, trade, vol, reason, false);
    remainingToClose -= vol;
    if (remainingToClose > 0 && trade.remainingVol > 0) {
      await sleep(chunkDelayMs);
    } else {
      break;
    }
  }
}

// Close position via market order (from spread.js)
async function closePositionMarket(symbol, pos, flash = true, overrideVol = null, retryCount = 0) {
  const side = pos.positionType === 1 ? 4 : 2; // 1=long -> close with short(4), 2=short -> close with long(2)
  const close_type = 5; // market close
  const position_id = pos.positionId;
  const leverage = pos.leverage || 20;

  if (closed_positions.has(String(position_id))) {
    logInfo(`Position ${position_id} on ${symbol} already closed via WS, skipping market close.`);
    return true;
  }
  const hold_vol = overrideVol || (positions[String(position_id)] ? positions[String(position_id)].holdVol : 0);
  if (!hold_vol || hold_vol <= 0) {
    logInfo(`Position ${position_id} on ${symbol} has zero holdVol, skipping market close.`);
    return true;
  }
  
  // Cancel TP order if it exists before closing position (only on first call, not partial closes)
  if (!overrideVol && positionTpOrders[String(position_id)]) {
    const tpOrderIds = positionTpOrders[String(position_id)];
    for (const tpOrderId of tpOrderIds) {
      logInfo(`Canceling Take Profit order ${tpOrderId} before closing position ${position_id}`);
      try {
        await cancelOrder(MEXC_KEY, tpOrderId);
      } catch (err) {
        logWarn(`Failed to cancel TP order ${tpOrderId} for position ${position_id}: ${err.message || err}`);
      }
    }
    delete positionTpOrders[String(position_id)];
  }
  
  const req = {
    symbol,
    side,
    openType: pos.openType || (getActiveTrade(symbol)?.strategy === 'gmgn' ? 2 : 1), // Use openType from position, default: GMGN cross (2), FAIR isolated (1)
    type: String(close_type),
    vol: hold_vol,
    leverage,
    positionId: position_id,
    priceProtect: "0",
    flashClose: true,
    ts: Date.now(),
    marketCeiling: 'false'
  };
  // Place order first
  const resp = await placeOrder(MEXC_KEY, req, flash);
  
  // Display market close information after order placement
  const currentTime = getCurrentTime();
  logInfo(`Attempting MARKET close of position ${position_id} on ${symbol} with vol ${hold_vol}${flash ? ' (flashClose)' : ''}`);
  logInfo(`Market close order response: ${JSON.stringify(resp)}`);

  // Handle max position size errors - close in parts
  if (resp && resp.success === false) {
    // Code 8819: "Exceeded the maximum number of contracts X that can be held at this leverage"
    if (resp.code === 8819 && resp._extend && resp._extend.amount) {
      const maxVol = parseInt(resp._extend.amount, 10);
      if (maxVol > 0 && maxVol < hold_vol) {
        logWarn(`⚠️ Position ${position_id} exceeds max contracts (${hold_vol} > ${maxVol}). Closing in parts...`);
        
        // Close first part with max allowed volume
        logInfo(`📦 Closing PART 1: ${maxVol} contracts of ${hold_vol} total`);
        await closePositionMarket(symbol, pos, flash, maxVol);
        
        // Wait briefly for the partial close to process
        await sleep(300);
        
        // Close remaining part
        const remainingVol = hold_vol - maxVol;
        if (remainingVol > 0 && !closed_positions.has(String(position_id))) {
          logInfo(`📦 Closing PART 2: ${remainingVol} remaining contracts`);
          await closePositionMarket(symbol, pos, flash, remainingVol);
        }
        return true;
      }
    }
    
    // Code 2051: "Exceeds the maximum order amount allowed for a single order"
    // We don't know the max, so try with half
    if (resp.code === 2051 && hold_vol > 1) {
      const halfVol = Math.floor(hold_vol / 2);
      logWarn(`⚠️ Position ${position_id} exceeds max order amount. Trying with half: ${halfVol} contracts`);
      
      // Close first half
      logInfo(`📦 Closing PART 1: ${halfVol} contracts (half of ${hold_vol})`);
      await closePositionMarket(symbol, pos, flash, halfVol);
      
      // Wait briefly
      await sleep(300);
      
      // Close second half
      const secondHalf = hold_vol - halfVol;
      if (secondHalf > 0 && !closed_positions.has(String(position_id))) {
        logInfo(`📦 Closing PART 2: ${secondHalf} remaining contracts`);
        await closePositionMarket(symbol, pos, flash, secondHalf);
      }
      return true;
    }
    
    // Code 510: "Requests are too frequent" - rate limiting, retry after short delay
    if (resp.code === 510 && retryCount < 3) {
      logWarn(`⚠️ Rate limited (510) closing position ${position_id} on ${symbol}. Retry ${retryCount + 1}/3 in 1s...`);
      await sleep(1000);
      // Retry closing with incremented retry counter
      if (!closed_positions.has(String(position_id))) {
        return await closePositionMarket(symbol, pos, flash, overrideVol, retryCount + 1);
      }
      return true;
    } else if (resp.code === 510) {
      logError(`❌ Rate limited (510) closing position ${position_id} on ${symbol} - max retries reached.`);
    }
    
    // Code 2009: "Position is nonexistent or closed" - already closed on exchange
    if (resp.code === 2009) {
      logInfo(`✅ Position ${position_id} on ${symbol} already closed on exchange (code 2009). Cleaning up local state.`);
      // Mark as closed to stop further retry attempts
      closed_positions.add(String(position_id));
      delete positions[String(position_id)];
      delete positionOpenPrices[String(position_id)]; // Clean up positionOpenPrices for GMGN strategy
      // Clean up symbolPositions
      const symbolPosMap = symbolPositions.get(symbol);
      if (symbolPosMap) {
        symbolPosMap.delete(String(position_id));
      }
      return true;
    }
  }

  // Запускаем проверку через 10 секунд - закрылась ли позиция по WebSocket (only for non-partial closes)
  if (!overrideVol) {
    setTimeout(async () => {
      // Проверяем через WS: если позиция все еще открыта, закрываем снова
      if (!closed_positions.has(String(position_id)) && positions[String(position_id)]) {
        const currentPos = positions[String(position_id)];
        if (currentPos.holdVol > 0 && currentPos.state !== 3) {
          logWarn(`⚠️ Position ${position_id} still OPEN after 10s (holdVol: ${currentPos.holdVol}). Retrying market close...`);
          // Рекурсивно вызываем закрытие снова
          await closePositionMarket(symbol, currentPos, flash);
        }
      }
    }, 10000);
  }

  return true;
}

// Schedule position closer (from spread.js)
const closure_tasks = {}; // positionId -> Promise
async function schedulePositionCloser(symbol, pos, method = "market", flashClose = true) {
  const pid = String(pos.positionId);
  if (closed_positions.has(pid)) {
    return; // Уже закрыта по WS - молча пропускаем
  }

  // Проверяем, не запущена ли уже задача закрытия для этой позиции
  if (closure_tasks[pid]) {
    return; // Уже запущена - пропускаем, чтобы не было спама
  }

  // Запускаем задачу закрытия (она сама будет повторять попытки каждые 10 сек через WS)
  closure_tasks[pid] = closePositionMarket(symbol, pos, flashClose);
}

// ---------------------- GMGN spread trading (TP) logic -----------------------------
async function checkGmgnSpreadAndTrade(symbol, gmgnPrice, gmgnVolume) {
  if (!ENABLE_GMGN_SPREAD_TRADING) {
    logGmgnSkip(symbol || 'unknown', 'GMGN strategy disabled', null, 120000);
    return;
  }
  if (!symbol) {
    logGmgnSkip('unknown', 'missing symbol in GMGN signal', null, 120000);
    return;
  }
  const gmgnPriceNum = Number(gmgnPrice);
  if (!Number.isFinite(gmgnPriceNum) || gmgnPriceNum <= 0) {
    logGmgnSkip(symbol, 'invalid GMGN price', { gmgnPrice }, 60000);
    return;
  }

  // Basic symbol checks
  if (BLACKLISTED_SYMBOLS.has(symbol)) {
    logGmgnSkip(symbol, 'hard blacklist');
    return;
  }
  if (isTickerBlacklisted(symbol)) {
    logGmgnSkip(symbol, 'ticker blacklist');
    return;
  }
  const normalizedSymbol = normalizeBlacklistTicker(symbol);
  if (normalizedSymbol && STOPLOSS_BLACKLIST.has(normalizedSymbol)) {
    logGmgnSkip(symbol, 'stop-loss blacklist');
    return; // Check stop-loss banlist
  }
  if (ENABLE_DEPOSIT_WITHDRAW_CHECK && isDepositWithdrawBlacklisted(symbol)) {
    logGmgnSkip(symbol, 'deposit/withdraw blacklist');
    return;
  }

  // Block symbol for BOTH strategies if there is already an active trade or an in-flight open.
  // This prevents FAIR and GMGN from opening simultaneously on the same ticker.
  if (getActiveTrade(symbol)) {
    logGmgnSkip(symbol, 'active trade already exists');
    return;
  }
  if (inFlightOpens.has(symbol)) {
    logGmgnSkip(symbol, 'open order is in-flight');
    return;
  }
  if (flagManualHoldIfLive(symbol)) {
    logGmgnSkip(symbol, 'manual/live position hold');
    return;
  }

  const cfg = gmgnConfigBySymbol.get(symbol);
  if (!cfg) {
    logGmgnSkip(symbol, 'missing GMGN token config');
    return; // not configured for GMGN trading
  }

  const ob = orderbooks[symbol];
  if (!ob || !ob.best_buy || !ob.best_sell) {
    stats.opportunitiesSkippedNoOrderbook++;
    ensureOrderbookUpdaterStarted(symbol, 'gmgn-signal-missing-ob');
    const depthAgeMs = ob && ob.depthTs ? (Date.now() - ob.depthTs) : null;
    logGmgnSkip(
      symbol,
      'orderbook not ready',
      {
        bestBuy: ob?.best_buy ?? null,
        bestSell: ob?.best_sell ?? null,
        depthAgeMs
      },
      20000
    );
    return;
  }

  // Volume filter removed for GMGN (as in spread.js)

  const spreadThreshold = (Number(cfg.percentagecountforopen) || DEFAULT_OPEN_THRESHOLD) / 100;

  // Down spread: MEXC bid > GMGN => open SHORT on MEXC (sell at bid)
  const downSpread = (ob.best_buy - gmgnPriceNum) / ob.best_buy;
  // Up spread: GMGN > MEXC ask => open LONG on MEXC (buy at ask)
  const upSpread = (gmgnPriceNum - ob.best_sell) / ob.best_sell;

  // Track top spreads (GMGN) continuously (not only when crossing open threshold)
  if (downSpread >= upSpread) {
    updateTopSpreads(symbol, downSpread, 'SHORT', 'GMGN');
  } else {
    updateTopSpreads(symbol, upSpread, 'LONG', 'GMGN');
  }

  if (downSpread >= spreadThreshold) {
    stats.opportunitiesFound++;
    stats.opportunitiesFoundGmgn++;
    stats.opportunitiesUSDT++;
    stats.tradeExecutionsStarted++;
    stats.tradeExecutionsStartedGmgn++;
    await openTradeFromSignal({
      symbol,
      strategy: 'gmgn',
      isLong: false,
      entryPrice: ob.best_buy,
      referencePrice: gmgnPriceNum,
      initialSpread: downSpread,
      openType: 2, // Cross for GMGN (2=cross, 1=isolated)
      leverageOverride: Number(cfg.leverage ?? GMGN_DEFAULT_LEVERAGE),
      marginOverride: Number(available_balance) * (GMGN_FIXED_MARGIN_PERCENT / 100),
      cooldownMs: GMGN_LAST_CLOSE_DIRECTION_COOLDOWN_MS,
      applySlippageCap: false,
      maxDrawdownPercent: (Number(cfg.maxDrawdown ?? 8) / 100),
      // TP via placeTakeProfitLimitOrder (from spread.js) - placed in handlePositionUpdate
      takeProfitPercentForOrder: 0,
      skipTpLimitPlacement: true
    });
  } else if (upSpread >= spreadThreshold) {
    stats.opportunitiesFound++;
    stats.opportunitiesFoundGmgn++;
    stats.opportunitiesUSDT++;
    stats.tradeExecutionsStarted++;
    stats.tradeExecutionsStartedGmgn++;
    await openTradeFromSignal({
      symbol,
      strategy: 'gmgn',
      isLong: true,
      entryPrice: ob.best_sell,
      referencePrice: gmgnPriceNum,
      initialSpread: upSpread,
      openType: 2, // Cross for GMGN (2=cross, 1=isolated)
      leverageOverride: Number(cfg.leverage ?? GMGN_DEFAULT_LEVERAGE),
      marginOverride: Number(available_balance) * (GMGN_FIXED_MARGIN_PERCENT / 100),
      cooldownMs: GMGN_LAST_CLOSE_DIRECTION_COOLDOWN_MS,
      applySlippageCap: false,
      maxDrawdownPercent: (Number(cfg.maxDrawdown ?? 8) / 100),
      // TP via placeTakeProfitLimitOrder (from spread.js) - placed in handlePositionUpdate
      takeProfitPercentForOrder: 0,
      skipTpLimitPlacement: true
    });
  } else {
    logGmgnSkip(
      symbol,
      'spread below open threshold',
      {
        gmgnVolume: Number.isFinite(Number(gmgnVolume)) ? Number(gmgnVolume) : null,
        downSpreadPct: Number((downSpread * 100).toFixed(4)),
        upSpreadPct: Number((upSpread * 100).toFixed(4)),
        thresholdPct: Number((spreadThreshold * 100).toFixed(4))
      },
      45000
    );
  }
}

async function monitorGmgnPositionsForClosure(symbol, gmgnPrice) {
  // Проверяем закрытие позиций GMGN только на свежих обновлениях от GMGN WebSocket
  // Не используем кеш, чтобы избежать устаревших цен
  if (!gmgnPrice) return;
  
  const ob = orderbooks[symbol];
  if (!ob || !ob.best_buy || !ob.best_sell) return;

  const cfg = gmgnConfigBySymbol.get(symbol);
  if (!cfg) return;

  const normalSpreadClosure = (Number(cfg.normalSpreadClosure ?? 0.5) / 100);
  const adverseSpreadThreshold = 1.0 / 100; // 1% неблагоприятное изменение спреда

  // Optimized: use symbolPositions Map to iterate only positions for this symbol
  const symbolPosMap = symbolPositions.get(symbol);
  if (!symbolPosMap || symbolPosMap.size === 0) return;

  for (const pos_id of symbolPosMap.keys()) {
    const pos = positions[pos_id];
    if (!pos || closed_positions.has(String(pos_id))) continue;
    if (!pos.holdVol || pos.holdVol <= 0) continue;

    const isLong = pos.positionType === 1;

    // Get position entry info for timeout check
    const openInfo = positionOpenPrices[pos_id];
    if (!openInfo) continue;
    
    const entryTime = openInfo.entryTime || Date.now();
    const elapsed = Date.now() - entryTime;
    
    // Check: Timeout (45 minutes) - kill switch
  if (elapsed >= MAX_POSITION_DURATION_MS) {
      logInfo(`⏱️ Timeout (45min) for position ${pos_id} on ${symbol}. Closing position.`);
      await schedulePositionCloser(symbol, pos, "market", true);
      continue;
  }

    // Check: Spread closure (spread has equalized)
    // For LONG: opened when GMGN > MEXC ask, close when spread <= normalSpreadClosure
    // For SHORT: opened when MEXC bid > GMGN, close when spread <= normalSpreadClosure
    const currentSpread = isLong
      ? (gmgnPrice - ob.best_sell) / ob.best_sell  // LONG: opened when GMGN > MEXC ask
      : (ob.best_buy - gmgnPrice) / ob.best_buy;   // SHORT: opened when MEXC bid > GMGN

    if (currentSpread <= normalSpreadClosure) {
      logInfo(`Spread equalized for position ${pos_id} on ${symbol} (spread: ${(currentSpread*100).toFixed(2)}% <= ${(normalSpreadClosure*100).toFixed(2)}%). Closing position.`);
      await schedulePositionCloser(symbol, pos, "market", true);
      continue;
  }

    // Check: Adverse spread movement (спред пошел в противоположную сторону)
    // SHORT: открыли когда GMGN < MEXC (минусовой спред), закрываем если GMGN > MEXC на 1%
    // LONG: открыли когда GMGN > MEXC (плюсовой спред), закрываем если GMGN < MEXC на 1%
    if (isLong) {
      // LONG: открыт когда GMGN был выше MEXC, проверяем не стал ли GMGN ниже на 1%
      const adverseSpread = (ob.best_sell - gmgnPrice) / ob.best_sell;
      if (adverseSpread >= adverseSpreadThreshold) {
        logInfo(`⚠️ ADVERSE SPREAD for LONG position ${pos_id} on ${symbol}! GMGN dropped below MEXC by ${(adverseSpread*100).toFixed(2)}%. Emergency closing!`);
        await schedulePositionCloser(symbol, pos, "market", true);
        continue;
    }
  } else {
      // SHORT: открыт когда GMGN был ниже MEXC, проверяем не стал ли GMGN выше на 1%
      const adverseSpread = (gmgnPrice - ob.best_buy) / ob.best_buy;
      if (adverseSpread >= adverseSpreadThreshold) {
        logInfo(`⚠️ ADVERSE SPREAD for SHORT position ${pos_id} on ${symbol}! GMGN rose above MEXC by ${(adverseSpread*100).toFixed(2)}%. Emergency closing!`);
        await schedulePositionCloser(symbol, pos, "market", true);
        continue;
      }
    }
  }
}

async function manageOpenTrade(symbol, markPrice, ob, lastPrice, nowTs) {
  const trade = getActiveTrade(symbol);
  if (!trade) {
    return;
  }

  // GMGN strategy has its own exit logic (based on GMGN/MEXC spread)
  // Проверка закрытия позиций GMGN происходит только при свежих обновлениях от GMGN WebSocket
  // Не проверяем по кешу, чтобы избежать использования устаревших цен
  if (trade.strategy === 'gmgn') {
    return;
  }

  if (!markPrice) {
    return;
  }

  // Require confirmed position before managing exits to avoid early reduce-only orders
  const symbolPosMap = symbolPositions.get(symbol);
  const hasLivePos = symbolPosMap && [...symbolPosMap.values()].some(p => p.holdVol > 0 && !closed_positions.has(p.positionId || ""));
  if (!trade.positionId && !hasLivePos) {
    return;
  }

  const obFresh = isOrderbookFresh(ob, nowTs);
  const exitPrice = computeExitPrice(trade, obFresh ? ob : null, lastPrice);
  const elapsed = Date.now() - trade.entryTime;

  // Kill switch: enforce timeout even if exitPrice is missing
  if (elapsed >= MAX_POSITION_DURATION_MS) {
    if (!trade.killSwitchTriggered) {
      logWarn(`   ⏱️ Kill switch closing ${symbol} (held ${(elapsed/1000).toFixed(1)}s)`);
      trade.killSwitchTriggered = true;
    }
    const killExit = exitPrice || markPrice || trade.entryPrice;
    if (killExit && killExit > 0 && computePnlPercent(trade, killExit) < 0) {
      recordLastCloseTimestamp(symbol, trade.isLong);
    }
    await closeWithMaxVol(symbol, trade, trade.remainingVol, 'timeout');
    return;
  }

  if (!exitPrice || exitPrice <= 0) {
    return;
  }

  const spreadPercent = Math.abs(markPrice - exitPrice) / exitPrice;
  const pnlPercent = computePnlPercent(trade, exitPrice);
  
  // Check if spread is still workable (above threshold for opening new positions)
  const threshold = trade.isLong ? FAIR_PRICE_THRESHOLD_LONG : FAIR_PRICE_THRESHOLD_SHORT;
  const spreadWorkable = spreadPercent >= threshold;
  
  // Determine if spread has converged (needs closing)
  const spreadConverged = spreadPercent <= SPREAD_FINAL_CLOSE_THRESHOLD ||
    (trade.isLong && markPrice <= exitPrice) ||
    (!trade.isLong && markPrice >= exitPrice);
  const spreadPartiallyConverged = spreadPercent <= SPREAD_PARTIAL_CLOSE_THRESHOLD;

  // If spread became workable again, stop closing attempts and reset retry counter
  if (spreadWorkable && trade.pendingCloseVol > 0) {
    logInfo(`   ✅ Spread for ${symbol} became workable again (${(spreadPercent * 100).toFixed(2)}% >= ${(threshold * 100).toFixed(2)}%), stopping close attempts`);
    trade.pendingCloseVol = 0;
    trade.closeRetries = 0;
    trade.pendingCloseReason = null;
    trade.lastCloseAttempt = null;
  }

  // Retry closing if spread is still converged and position is not closed
  // Continue retrying indefinitely until position is closed or spread becomes workable
  if (trade.pendingCloseVol > 0 && trade.lastCloseAttempt && 
      (Date.now() - trade.lastCloseAttempt) > CLOSE_RETRY_INTERVAL_MS && 
      (spreadConverged || spreadPartiallyConverged) && 
      !spreadWorkable) {
    trade.closeRetries++;
    logWarn(`   ⏳ Re-issuing close for ${symbol} (attempt ${trade.closeRetries}, spread=${(spreadPercent * 100).toFixed(2)}%, threshold=${(threshold * 100).toFixed(2)}%)`);
    await requestClosePosition(symbol, trade, trade.pendingCloseVol, `${trade.pendingCloseReason || 'retry'}-retry`, true);
  }

  if (trade.remainingVol <= 0) {
    finalizeActiveTrade(symbol, "volume-zero");
    return;
  }

  // If spread became workable, don't close position
  if (spreadWorkable) {
    // Reset partial close flag if spread became workable again
    if (trade.partialCloseRequested && !spreadPartiallyConverged) {
      trade.partialCloseRequested = false;
      logInfo(`   ✅ Spread for ${symbol} recovered, resetting partial close flag`);
    }
    return;
  }

  if (!trade.partialCloseRequested && spreadPartiallyConverged) {
    const closeVol = trade.openVol * PARTIAL_CLOSE_RATIO;
    await closeWithMaxVol(symbol, trade, closeVol, 'partial-spread');
    trade.partialCloseRequested = true;
    return;
  }

  if (spreadConverged) {
    if (pnlPercent < 0) recordLastCloseTimestamp(symbol, trade.isLong);
    await closeWithMaxVol(symbol, trade, trade.remainingVol, 'spread-converged');
    return;
  }

  if (elapsed >= MAX_POSITION_DURATION_MS) {
    if (!trade.killSwitchTriggered) {
      logWarn(`   ⏱️ Kill switch closing ${symbol} (held ${(elapsed/1000).toFixed(1)}s)`);
      trade.killSwitchTriggered = true;
    }
    if (pnlPercent < 0) recordLastCloseTimestamp(symbol, trade.isLong);
    await closeWithMaxVol(symbol, trade, trade.remainingVol, 'timeout');
  }

  if (pnlPercent <= -MAX_DRAWDOWN_PERCENT) {
    if (!trade.killSwitchTriggered) {
      logWarn(`   ⚠️ Drawdown ${ (pnlPercent * 100).toFixed(2) }% on ${symbol}, closing.`);
      trade.killSwitchTriggered = true;
    }
    recordLastCloseTimestamp(symbol, trade.isLong);
    await closeWithMaxVol(symbol, trade, trade.remainingVol, 'drawdown');
  }
}

// Position tracking
let positions = {};                      // positionId -> position data via WS
let closed_positions = new Set();        // mark closed only after WS confirms
const realizedPnlCountedPositionIds = new Set(); // positionIds already counted into realized PnL totals
let symbolPositions = new Map();         // symbol -> Map<positionId, {positionType, holdVol}>
let balanceRefreshInProgress = false;    // prevent overlapping balance refreshes
const manualPositionHold = new Set();    // symbols with manual/open positions to skip trading
const manualHoldUntil = new Map();       // symbol -> timestamp until which we skip trading (e.g., after 8819)

// Statistics
let stats = {
  totalMessagesReceived: 0, // Number of batch messages received
  totalTickersReceived: 0, // Total number of ticker updates (all symbols in all batches)
  totalTickersProcessed: 0,
  opportunitiesFound: 0, // All opportunities (FAIR + GMGN, USDT and non-USDT)
  opportunitiesFoundFair: 0,
  opportunitiesFoundGmgn: 0,
  opportunitiesFoundSpotFutures: 0, // Spot-futures opportunities passing open threshold
  opportunitiesUSDT: 0, // USDT opportunities only
  opportunitiesNonUSDT: 0, // Non-USDT opportunities (tracked but not traded)
  opportunitiesSkippedNoOrderbook: 0, // Opportunities skipped due to missing orderbook data
  opportunitiesSkippedDisabled: 0, // Opportunities skipped because direction is disabled
  orderbooksReady: 0, // Number of symbols with loaded orderbook data
  tradeExecutionsStarted: 0, // Number of times trade execution was started
  tradeExecutionsStartedFair: 0,
  tradeExecutionsStartedGmgn: 0,
  spotFuturesTradesOpened: 0, // Number of spot-futures arbitrage positions successfully opened
  spotFuturesTradesClosed: 0, // Number of spot-futures arbitrage positions successfully closed
  realizedPnlFair: 0, // Cumulative realized PnL for FAIR trades (USDT)
  realizedPnlFairLong: 0, // Cumulative realized PnL for FAIR LONG trades (USDT)
  realizedPnlFairShort: 0, // Cumulative realized PnL for FAIR SHORT trades (USDT)
  realizedCountFairLong: 0, // Cumulative count of FAIR LONG trades (closed)
  realizedCountFairShort: 0, // Cumulative count of FAIR SHORT trades (closed)
  realizedPnlGmgn: 0, // Cumulative realized PnL for GMGN trades (USDT)
  realizedPnlGmgnLong: 0, // Cumulative realized PnL for GMGN LONG trades (USDT)
  realizedPnlGmgnShort: 0, // Cumulative realized PnL for GMGN SHORT trades (USDT)
  realizedCountGmgnLong: 0, // Cumulative count of GMGN LONG trades (closed)
  realizedCountGmgnShort: 0, // Cumulative count of GMGN SHORT trades (closed)
  realizedPnlSpotFutures: 0, // Cumulative realized PnL for SPOT-FUTURES arbitrage (USDT)
  realizedCountSpotFutures: 0, // Cumulative count of SPOT-FUTURES trades (closed)
  ordersPlaced: 0,
  ordersPlacedFair: 0,
  ordersPlacedGmgn: 0,
  ordersFailed: 0,
  ordersFailedFair: 0,
  ordersFailedGmgn: 0,
  orderFailReasons: new Map(), // Map of failure reason -> count (e.g., "maxVol=0" -> 1, "API error 510" -> 2)
  maxSpreadFound: 0,
  maxSpreadSymbol: null,
  maxSpreadDirection: null, // Direction (LONG/SHORT) of max spread found
  currentMaxSpread: 0, // Current maximum spread among all tracked symbols
  currentMaxSpreadSymbol: null, // Symbol with current max spread
  currentMaxSpreadDirection: null, // Direction (LONG/SHORT) of current max spread
  topSpreads: [], // Array of {key, symbol, spread, direction, source} for top 5 spreads (FAIR/GMGN)
  topSpotFuturesSpreads: [], // Array of {key, spotSymbol, futuresSymbol, spread} for top 5 spot-futures spreads
  lastWebSocketUpdate: null,
  lastStatusUpdate: Date.now()
};

// Helper function to get current time
function getCurrentTime() {
  const now = new Date();
  const hours = String(now.getHours()).padStart(2, '0');
  const minutes = String(now.getMinutes()).padStart(2, '0');
  const seconds = String(now.getSeconds()).padStart(2, '0');
  const milliseconds = String(now.getMilliseconds()).padStart(3, '0');
  return `${hours}:${minutes}:${seconds}.${milliseconds}`;
}

function logLine(level, message) {
  const timestamp = getCurrentTime();
  const line = `[${timestamp}] ${message}`;
  console[level](line);
  try {
    logStream.write(line + '\n');
  } catch (err) {
    // ignore logging errors to file to avoid crashing
  }
}

function logInfo(message) {
  logLine('info', message);
}

function logWarn(message) {
  logLine('warn', message);
}

function logError(message) {
  logLine('error', message);
}

function _spreadSourceTag(source) {
  const s = String(source || '').toUpperCase();
  if (s === 'GMGN') return 'GMGN';
  return 'FAIR';
}

function _makeTopSpreadKey(symbol, source) {
  return `${String(symbol || '').toUpperCase()}::${_spreadSourceTag(source)}`;
}

function updateTopSpreads(symbol, spread, direction, source) {
  const s = Number(spread);
  if (!Number.isFinite(s) || s <= 0) return;
  const src = _spreadSourceTag(source);
  const key = _makeTopSpreadKey(symbol, src);

  const entry = {
    key,
    symbol,
    spread: s,
    direction: direction === 'SHORT' ? 'SHORT' : 'LONG',
    source: src
  };

  const existingIndex = stats.topSpreads.findIndex(x => x.key === key);
  if (existingIndex >= 0) {
    stats.topSpreads[existingIndex] = entry;
  } else {
    stats.topSpreads.push(entry);
  }

  stats.topSpreads.sort((a, b) => b.spread - a.spread);
  stats.topSpreads.splice(5);
}

function _makeTopSpotFuturesKey(spotSymbol, futuresSymbol) {
  return `${String(spotSymbol || '').toUpperCase()}::${String(futuresSymbol || '').toUpperCase()}`;
}

function updateTopSpotFuturesSpreads(spotSymbol, futuresSymbol, spread) {
  const s = Number(spread);
  if (!Number.isFinite(s) || s <= 0) return;

  const key = _makeTopSpotFuturesKey(spotSymbol, futuresSymbol);
  const entry = { key, spotSymbol, futuresSymbol, spread: s };

  const arr = stats.topSpotFuturesSpreads || (stats.topSpotFuturesSpreads = []);
  const existingIndex = arr.findIndex(x => x.key === key);
  if (existingIndex >= 0) {
    arr[existingIndex] = entry;
  } else {
    arr.push(entry);
  }

  arr.sort((a, b) => b.spread - a.spread);
  arr.splice(5);
}

// MD5 Hash
function md5(val) {
  return crypto.createHash('md5').update(val, 'utf8').digest("hex");
}

// Cancel order (from spread.js)
async function cancelOrder(key, orderId) {
  const obj = [orderId];
  const sig = signReq(key, obj);
  const headersObj = {
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Content-Type": "application/json;charset=UTF-8",
    "Origin": "https://www.mexc.com",
    "Referer": "https://www.mexc.com/",
    "User-Agent": USER_AGENT,
    "Sec-Ch-Ua": '"Chromium";v="120", "Not_A Brand";v="8"',
    "Sec-Ch-Ua-Mobile": "?0",
    "Sec-Ch-Ua-Platform": '"Windows"',
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
    "x-mxc-sign": sig.sign,
    "x-mxc-nonce": sig.time,
    "Authorization": key
  };

  try {
    const response = await axios.post(
      'https://futures.mexc.com/api/v1/private/order/cancel',
      obj,
      { headers: headersObj, timeout: 15000 }
    );
    logInfo(`Cancel order response for ${orderId}: ${JSON.stringify(response.data)}`);
    return response.data;
  } catch (err) {
    logError(`Failed to cancel order ${orderId}: ${err.message || err}`);
    return null;
  }
}

// Sign request for MEXC API
function signReq(key, obj) {
  const now = String(Date.now());
  const g = md5(key + now).substr(7);
  const s = JSON.stringify(obj);
  const sign = md5(now + s + g);
  return { time: now, sign };
}

// Place order
async function placeOrder(key, obj) {
  const sig = signReq(key, obj);
  const headers = {
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Content-Type": "application/json;charset=UTF-8",
    "Origin": "https://www.mexc.com",
    "Referer": "https://www.mexc.com/",
    "User-Agent": USER_AGENT,
    "Sec-Ch-Ua": '"Chromium";v="120", "Not_A Brand";v="8"',
    "Sec-Ch-Ua-Mobile": "?0",
    "Sec-Ch-Ua-Platform": '"Windows"',
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
    "x-mxc-sign": sig.sign,
    "x-mxc-nonce": sig.time,
    "Authorization": key
  };

  try {
    const response = await axios.post(
      'https://futures.mexc.com/api/v1/private/order/create',
      obj,
      { headers, timeout: 15000 }
    );
    return response.data;
  } catch (err) {
    logError(`Error placing order: ${err.message || err}`);
    return null;
  }
}

// Get symbol scale
function getSymbolScale(symbol) {
  const detail = contract_details[symbol];
  if (!detail) return [0, 0, null];
  // Use override if available, otherwise use detail.maxVol
  const maxVol = contractMaxVolOverrides[symbol] !== undefined
    ? contractMaxVolOverrides[symbol]
    : detail.maxVol;
  return [detail.priceScale, detail.volScale, maxVol];
}

// Count total number of open positions across all symbols
function getTotalOpenPositions() {
  let total = 0;
  for (const [symbol, symbolPosMap] of symbolPositions) {
    if (symbolPosMap && symbolPosMap.size > 0) {
      // Count only positions that are not closed
      for (const [pos_id, posInfo] of symbolPosMap) {
        if (posInfo.holdVol > 0 && !closed_positions.has(pos_id)) {
          total++;
        }
      }
    }
  }
  return total;
}

// Handle position updates from WebSocket
async function handlePositionUpdate(pos) {
  const symbol = pos.symbol;
  const pos_id = String(pos.positionId);
  if (pos.state === 3) {
    // closed - WebSocket confirmed closure
    logInfo(`✅ Position ${pos_id} on ${symbol} CLOSED via WebSocket (state=3).`);
    
    // Cancel TP order if it exists and hasn't been filled (for GMGN strategy)
    if (positionTpOrders[pos_id]) {
      const tpOrderIds = positionTpOrders[pos_id];
      for (const tpOrderId of tpOrderIds) {
        logInfo(`Canceling Take Profit order ${tpOrderId} for closed position ${pos_id}`);
        try {
          await cancelOrder(MEXC_KEY, tpOrderId);
        } catch (err) {
          logWarn(`Failed to cancel TP order ${tpOrderId} for position ${pos_id}: ${err.message || err}`);
        }
      }
      delete positionTpOrders[pos_id];
    }
    
    delete positions[pos_id];
    closed_positions.add(pos_id);
    delete positionOpenPrices[pos_id]; // Clean up positionOpenPrices for GMGN strategy

    // Remove from optimized symbolPositions Map
    const symbolPosMap = symbolPositions.get(symbol);
    if (symbolPosMap) {
      symbolPosMap.delete(pos_id);
      if (symbolPosMap.size === 0) {
        symbolPositions.delete(symbol);
        // Clear manual hold latch when no live positions remain
        manualPositionHold.delete(symbol);
      }
    }

    // If this was the active trade, assess PnL and set cooldown if loss
    const trade = getActiveTrade(symbol);
    if (trade && trade.positionId === pos_id) {
      // Count realized PnL once per positionId (from WS payload)
      if (!realizedPnlCountedPositionIds.has(pos_id)) {
        const realized = Number(
          pos.realised ?? pos.realized ?? pos.realisedPnl ?? pos.realizedPnl ?? pos.realise ?? 0
        );
        if (Number.isFinite(realized)) {
          const isLong = typeof trade.isLong === 'boolean'
            ? trade.isLong
            : (pos.positionType === 1);
          if (trade.strategy === 'gmgn') {
            stats.realizedPnlGmgn = (stats.realizedPnlGmgn || 0) + realized;
            if (isLong) stats.realizedPnlGmgnLong = (stats.realizedPnlGmgnLong || 0) + realized;
            else stats.realizedPnlGmgnShort = (stats.realizedPnlGmgnShort || 0) + realized;
            if (isLong) stats.realizedCountGmgnLong = (stats.realizedCountGmgnLong || 0) + 1;
            else stats.realizedCountGmgnShort = (stats.realizedCountGmgnShort || 0) + 1;
          } else {
            stats.realizedPnlFair = (stats.realizedPnlFair || 0) + realized;
            if (isLong) stats.realizedPnlFairLong = (stats.realizedPnlFairLong || 0) + realized;
            else stats.realizedPnlFairShort = (stats.realizedPnlFairShort || 0) + realized;
            if (isLong) stats.realizedCountFairLong = (stats.realizedCountFairLong || 0) + 1;
            else stats.realizedCountFairShort = (stats.realizedCountFairShort || 0) + 1;
          }
          realizedPnlCountedPositionIds.add(pos_id);
        }
      }

      // Get REALIZED PnL from exchange (most accurate)
      const realizedPnl = Number(
        pos.realised ?? pos.realized ?? pos.realisedPnl ?? pos.realizedPnl ?? pos.realise ?? 0
      );
      
      // Get margin for percentage calculation
      const margin = Number(trade.margin || pos.im || pos.margin || pos.initialMargin || 0);
      
      // Calculate PnL percentage based on margin (as exchange does)
      let pnlPercent = 0;
      if (margin > 0 && Number.isFinite(realizedPnl)) {
        pnlPercent = (realizedPnl / margin) * 100;
      } else {
        // Fallback: calculate from price difference
      const ob = orderbooks[symbol];
      const lastTicker = tickerData[symbol];
      const exitPrice = computeExitPrice(trade, ob, lastTicker?.lastPrice || null);
        pnlPercent = computePnlPercent(trade, exitPrice) * 100;
      }
      
      // Send close notification with real PnL
      sendTradeNotification({
        type: 'close',
        symbol: symbol,
        isLong: trade.isLong,
        pnl: realizedPnl,
        pnlPercent: pnlPercent,
        reason: 'closed',
        strategy: trade.strategy || 'fair'
      });
      
      if (pnlPercent < 0) {
        recordLastCloseTimestamp(symbol, trade.isLong);
        logInfo(`   📉 WS-closed ${symbol} (${trade.isLong ? 'LONG' : 'SHORT'}) with loss ${pnlPercent.toFixed(2)}%, cooldown applied.`);
        
        // Check for stop-loss trigger and banlist (only for GMGN strategy)
        if (trade.strategy === 'gmgn') {
          // Записать убыточное закрытие для отслеживания двух минусов подряд
          recordGmgnLoss(symbol, trade.isLong, realizedPnl);
          const stopLossThresholdPct = trade.isLong ? (LONG_STOP_LOSS_PERCENT / 100) : (GLOBAL_STOP_LOSS_PERCENT / 100);
          const isStopLossTriggered = pnlPercent <= -(stopLossThresholdPct * 100);
          
          const normalizedSymbol = normalizeBlacklistTicker(symbol);
          if (normalizedSymbol) {
            const { stopCount, netLoss } = recordStopLossOutcome(normalizedSymbol, isStopLossTriggered, pnlPercent, trade.isLong);
            
            // Check banlist conditions: 2 stop-losses OR 10% net loss for longs
            const shouldBanlist = (stopCount >= STOPLOSS_HISTORY_REQUIRED_SL || netLoss >= LONG_BANLIST_NET_LOSS_THRESHOLD) && !STOPLOSS_BLACKLIST.has(normalizedSymbol);
            
            if (isStopLossTriggered) {
              const posType = trade.isLong ? 'LONG' : 'SHORT';
              logWarn(`[STOPLOSS] ${symbol} ${posType}: stop-loss triggered (last ${STOPLOSS_HISTORY_SIZE} deals: ${stopCount} SL, net loss: ${netLoss.toFixed(2)}%).`);
            }
            
            if (shouldBanlist) {
              STOPLOSS_BLACKLIST.add(normalizedSymbol);
              persistStopLossBlacklist();
              // Also add to BLACKLISTED_TICKERS for GMGN strategy
              BLACKLISTED_TICKERS.add(normalizedSymbol);
              const reason = stopCount >= STOPLOSS_HISTORY_REQUIRED_SL 
                ? `${stopCount} SL within last ${STOPLOSS_HISTORY_SIZE} deals`
                : `${netLoss.toFixed(2)}% net loss (>= ${LONG_BANLIST_NET_LOSS_THRESHOLD}%)`;
              logError(`[STOPLOSS] ${symbol}: added to stop-loss banlist after ${reason}.`);
              
              // Close any remaining open positions for this ticker
              closeAllPositionsForSymbol(normalizedSymbol);
            }
          }
        }
      }
      
      // Send balance after closing
      setTimeout(async () => {
        try {
          await refreshBalance('position-close');
          if (balanceReady && Number.isFinite(available_balance)) {
            sendTradeNotification({
              type: 'balance',
              balance: available_balance,
              source: 'futures'
            });
          }
        } catch (err) {
          logError(`Failed to send balance after close: ${err.message}`);
      }
      }, 2000);
      
      finalizeActiveTrade(symbol, 'ws-closed');
    } else if (!trade) {
      // Position closed but was not tracked locally
      logWarn(`⚠️ Position ${pos_id} on ${symbol} closed but was not tracked locally!`);
      logWarn(`   Position data: holdVol=${pos.holdVol}, closeVol=${pos.closeVol}, closeAvgPrice=${pos.closeAvgPrice}, realised=${pos.realised}`);
      // Ensure cleanup even if not tracked
      finalizeActiveTrade(symbol, 'ws-closed-untracked');
    } else {
      // Trade exists but positionId doesn't match - different position
      finalizeActiveTrade(symbol, 'ws-closed');
    }
    await refreshBalance('position-close');
  } else {
    const isNew = !positions[pos_id];
    positions[pos_id] = pos;

    // Update optimized symbolPositions Map
    if (!symbolPositions.has(symbol)) {
      symbolPositions.set(symbol, new Map());
    }
    const symbolPosMap = symbolPositions.get(symbol);
    if (pos.holdVol > 0 && !closed_positions.has(pos_id)) {
      symbolPosMap.set(pos_id, {
        positionType: pos.positionType,
        holdVol: pos.holdVol
      });
    } else {
      symbolPosMap.delete(pos_id);
      if (symbolPosMap.size === 0) {
        symbolPositions.delete(symbol);
      }
    }

    const trade = getActiveTrade(symbol);
    if (trade) {
      const isOurPosition = trade.positionId === null && inFlightOpens.has(symbol);
      const isSamePosition = trade.positionId === pos_id;
      if (!isOurPosition && !isSamePosition) {
        // Another position on this symbol (e.g. manual) — don't touch it
        return;
      }
      if (isOurPosition) {
        trade.positionId = pos_id;
        clearInFlight(symbol);
        const posIsLong = pos.positionType === 1;
        const margin = Number(pos.im || pos.margin || pos.initialMargin || 0);
        const entryPrice = Number(pos.holdAvgPrice || pos.openAvgPrice || pos.avgEntryPrice || pos.openPrice || 0);
        sendTradeNotification({
          type: 'open',
          symbol: symbol,
          isLong: posIsLong,
          margin: margin > 0 ? margin : trade.margin,
          leverage: trade.leverage || pos.leverage || 20,
          entryPrice: entryPrice > 0 ? entryPrice : trade.entryPrice,
          strategy: trade.strategy || 'fair'
        });
      }
      
      // Verify position direction matches trade direction (safety check)
      const posIsLong = pos.positionType === 1;
      
      // Debug logging for position update
      // MEXC WebSocket uses holdAvgPrice/openAvgPrice, not avgEntryPrice/openPrice
      const entryPrice = pos.holdAvgPrice || pos.openAvgPrice || pos.avgEntryPrice || pos.openPrice || 'N/A';
      logInfo(`   🔍 Position update for ${symbol} (pos_id=${pos_id}): isNew=${isNew}, holdVol=${pos.holdVol || 'N/A'}, entryPrice=${entryPrice}, positionType=${pos.positionType} (${posIsLong ? 'LONG' : 'SHORT'}), trade.isLong=${trade.isLong}, trade.tpOrdersPlaced=${trade.tpOrdersPlaced}`);
      
      if (trade.isLong !== posIsLong) {
        logWarn(`   ⚠️ Position direction mismatch for ${symbol}: trade.isLong=${trade.isLong}, pos.positionType=${pos.positionType} (1=LONG). Skipping TP placement.`);
      }
      
      if (pos.holdVol !== undefined) {
        const newVol = Number(pos.holdVol);
        const prevVol = trade.lastKnownVol ?? trade.remainingVol ?? 0;
        trade.remainingVol = newVol;
        trade.lastKnownVol = newVol;
        
        // Check if position just opened (volume changed from 0 to > 0) OR if it's a new position
        const positionJustOpened = prevVol === 0 && newVol > 0;
        // Place TP if: (1) position just opened OR (2) it's a new position with volume > 0
        // AND TP not already placed AND direction matches
        // Note: We don't add fallback condition here to avoid conflicts with the retry logic below (line 5179)
        // The retry logic below handles cases where entry price becomes available later
        const shouldPlaceTP = (positionJustOpened || (isNew && newVol > 0)) && 
          !trade.tpOrdersPlaced && 
          trade.isLong === posIsLong;
        
        logInfo(`   🔍 TP placement check for ${symbol}: positionJustOpened=${positionJustOpened}, isNew=${isNew}, newVol=${newVol}, prevVol=${prevVol}, shouldPlaceTP=${shouldPlaceTP}, tpOrdersPlaced=${trade.tpOrdersPlaced}, directionMatch=${trade.isLong === posIsLong}`);
        
        if (newVol <= 0) {
          finalizeActiveTrade(symbol, 'position-flat');
        } else if (trade.pendingCloseVol > 0 && newVol < prevVol) {
          const filled = prevVol - newVol;
          trade.pendingCloseVol = Math.max(0, trade.pendingCloseVol - filled);
        }
        
        // Place TP orders when position is confirmed via WebSocket
        // This happens when: (1) position volume changes from 0 to > 0, OR (2) it's a new position with volume > 0
        // Only place if direction matches and TP not already placed
        if (shouldPlaceTP) {
          // CRITICAL: Use ONLY real average entry price from WebSocket, never fallback to trade.entryPrice
          // trade.entryPrice is the price at order placement, not the actual average fill price
          // MEXC WebSocket uses holdAvgPrice/openAvgPrice, not avgEntryPrice/openPrice
          const wsAvgEntryPrice = Number(pos.holdAvgPrice || pos.openAvgPrice || pos.avgEntryPrice || pos.openPrice || 0);
          const realVolume = newVol;
          const realLeverage = trade.leverage || getMaxLeverage(symbol);
          
          logInfo(`   🔍 TP placement attempt for ${symbol}: wsAvgEntryPrice=${wsAvgEntryPrice}, realVolume=${realVolume}, realLeverage=${realLeverage}`);
          
          // Only proceed if we have a valid average entry price from WebSocket
          if (wsAvgEntryPrice > 0 && realVolume > 0) {
            const priceSource = pos.holdAvgPrice ? 'holdAvgPrice' : (pos.openAvgPrice ? 'openAvgPrice' : (pos.avgEntryPrice ? 'avgEntryPrice' : (pos.openPrice ? 'openPrice' : 'UNKNOWN')));
            logInfo(`   🎯 Position confirmed via WebSocket - placing TP orders with real data: entry=${wsAvgEntryPrice.toFixed(8)} (from ${priceSource}), vol=${realVolume}, leverage=${realLeverage}x, direction=${posIsLong ? 'LONG' : 'SHORT'}`);
            logInfo(`   📊 WebSocket position data: holdAvgPrice=${pos.holdAvgPrice || 'N/A'}, openAvgPrice=${pos.openAvgPrice || 'N/A'}, holdVol=${pos.holdVol || 'N/A'}`);
            trade.tpOrdersPlaced = true; // Mark as placed to avoid duplicates
            
            // Use placeTakeProfitLimitOrder for GMGN strategy (from spread.js), placeTakeProfitLimits for FAIR
            if (trade.strategy === 'gmgn') {
              const cfg = gmgnConfigBySymbol.get(symbol);
              const takeProfitPercent = cfg?.takeProfitPercent || 5; // Default 5%
              // Use setTimeout with delay to avoid rate limits and ensure position data is fully available
              setTimeout(async () => {
                // Check if position is still open before placing TP order
                const currentPos = positions[pos_id];
                if (currentPos && currentPos.state !== 3 && !closed_positions.has(String(pos_id)) && currentPos.holdVol > 0) {
                  await placeTakeProfitLimitOrder(symbol, currentPos, takeProfitPercent);
                } else {
                  logInfo(`Position ${pos_id} closed before TP order could be placed.`);
                }
              }, 2000);
            } else {
            placeTakeProfitLimits(symbol, {
              isLong: posIsLong, // Use position direction from WebSocket, not trade (more reliable)
              volume: realVolume,
              entryPrice: wsAvgEntryPrice, // Use ONLY WebSocket average entry price
              leverage: realLeverage,
                openType: trade.openType || (trade.strategy === 'gmgn' ? 2 : 1), // GMGN: cross (2), FAIR: isolated (1)
                strategy: trade.strategy || 'fair' // Pass strategy for correct openType fallback
            }).catch(err => {
              logError(`❌ Error placing TP orders after position confirmation for ${symbol}: ${err.message}`);
              trade.tpOrdersPlaced = false; // Reset flag on error to allow retry
            });
            }
          } else {
            logWarn(`   ⚠️ Cannot place TP orders for ${symbol}: waiting for average entry price from WebSocket (current: holdAvgPrice=${pos.holdAvgPrice || 'N/A'}, openAvgPrice=${pos.openAvgPrice || 'N/A'}, fallback trade.entryPrice=${trade.entryPrice || 'N/A'})`);
            // Don't mark as placed, allow retry when WebSocket provides avgEntryPrice
            trade.tpOrdersPlaced = false;
          }
        } else if (isNew && newVol > 0) {
          // Log why TP wasn't placed for new positions
          logWarn(`   ⚠️ TP not placed for new position ${symbol}: positionJustOpened=${positionJustOpened}, tpOrdersPlaced=${trade.tpOrdersPlaced}, directionMatch=${trade.isLong === posIsLong}`);
        }
      } else {
        logWarn(`   ⚠️ Position update for ${symbol} has undefined holdVol: ${JSON.stringify(pos)}`);
      }
      // MEXC WebSocket uses holdAvgPrice/openAvgPrice, not avgEntryPrice/openPrice
      if (pos.holdAvgPrice || pos.openAvgPrice || pos.avgEntryPrice || pos.openPrice) {
        const newEntryPrice = Number(pos.holdAvgPrice || pos.openAvgPrice || pos.avgEntryPrice || pos.openPrice);
        const oldEntryPrice = trade.entryPrice;
        trade.entryPrice = newEntryPrice || trade.entryPrice;
        
        // If we now have a valid average entry price and TP wasn't placed yet, try to place it
        if (newEntryPrice > 0 && !trade.tpOrdersPlaced && trade.positionId && pos.holdVol > 0) {
          const realVolume = Number(pos.holdVol);
          const realLeverage = trade.leverage || getMaxLeverage(symbol);
          const priceSource = pos.holdAvgPrice ? 'holdAvgPrice' : (pos.openAvgPrice ? 'openAvgPrice' : (pos.avgEntryPrice ? 'avgEntryPrice' : 'openPrice'));
          
          logInfo(`   🔄 Average entry price now available for ${symbol}: ${newEntryPrice.toFixed(8)} (from ${priceSource}), attempting to place TP orders`);
          logInfo(`   📊 Previous entry price: ${oldEntryPrice ? oldEntryPrice.toFixed(8) : 'N/A'}, New entry price: ${newEntryPrice.toFixed(8)}`);
          
          trade.tpOrdersPlaced = true; // Mark as placed to avoid duplicates
          
          // Use placeTakeProfitLimitOrder for GMGN strategy (from spread.js), placeTakeProfitLimits for FAIR
          if (trade.strategy === 'gmgn') {
            const cfg = gmgnConfigBySymbol.get(symbol);
            const takeProfitPercent = cfg?.takeProfitPercent || 5; // Default 5%
            setTimeout(async () => {
              const currentPos = positions[pos_id];
              if (currentPos && currentPos.state !== 3 && !closed_positions.has(String(pos_id)) && currentPos.holdVol > 0) {
                await placeTakeProfitLimitOrder(symbol, currentPos, takeProfitPercent);
              }
            }, 2000);
          } else {
          placeTakeProfitLimits(symbol, {
            isLong: trade.isLong,
            volume: realVolume,
            entryPrice: newEntryPrice, // Use the real average entry price from WebSocket
            leverage: realLeverage,
              openType: trade.openType || (trade.strategy === 'gmgn' ? 2 : 1), // GMGN: cross (2), FAIR: isolated (1)
              strategy: trade.strategy || 'fair' // Pass strategy for correct openType fallback
          }).catch(err => {
            logError(`❌ Error placing TP orders after receiving average entry price for ${symbol}: ${err.message}`);
            trade.tpOrdersPlaced = false; // Reset flag on error to allow retry
          });
          }
        }
      }
    }

    if (isNew) {
      // Store opening prices for GMGN strategy (for timeout check)
      const trade = getActiveTrade(symbol);
      if (trade && trade.strategy === 'gmgn') {
        const tokenKey = gmgnSymbolToTokenKey[symbol];
        const gmgnPrice = tokenKey ? gmgnPrices[tokenKey] : null;
        const cfg = gmgnConfigBySymbol.get(symbol);
        const margin = Number(pos.im || pos.margin || pos.initialMargin || 0);
        const leverage = Number(pos.leverage || cfg?.leverage || 5);
        positionOpenPrices[pos_id] = {
          gmgnPrice: gmgnPrice,
          mexcPrice: pos.openAvgPrice || pos.openPrice,
          positionType: pos.positionType,
          margin: margin,
          leverage: leverage,
          entryTime: Date.now() // Store entry time for timeout check
        };
        logInfo(`Position ${pos_id} opened on ${symbol} (${pos.positionType === 1 ? "LONG" : "SHORT"}), margin=${margin}, leverage=${leverage}x`);
      } else {
      logInfo(`Position ${pos_id} opened on ${symbol} (${pos.positionType === 1 ? "LONG" : "SHORT"})`);
      }
    }

    // Position not in activeTrades — do not adopt and do not close (user's or other script's position)
    if (!trade && pos.holdVol > 0 && !closed_positions.has(pos_id)) {
      let arbMatch = null;
      for (const [, ap] of spotFuturesArbitragePositions) {
        if (ap && ap.status === 'open' && ap.futuresSymbol === symbol) {
          arbMatch = ap;
          break;
        }
      }
      if (arbMatch) {
        arbMatch.futuresPositionId = pos_id;
        logInfo(`[SPOT] 🧷 Linked futures position ${pos_id} to arbitrage ${arbMatch.arbitrageId} (${symbol})`);
      }
      // Do not recover and do not close — leave other positions untouched
    }
  }
}

// Get minimum margin for symbol
function getMinMargin(symbol) {
  const detail = contract_details[symbol];
  if (!detail) return DEFAULT_MIN_MARGIN_USDT;

  // Try to get minMargin from contract details
  // MEXC API may provide: minMargin, minNotional, minOrderValue, or minMarginRatio
  if (detail.minMargin !== undefined && detail.minMargin !== null) {
    return Number(detail.minMargin);
  }
  if (detail.minNotional !== undefined && detail.minNotional !== null) {
    return Number(detail.minNotional);
  }
  if (detail.minOrderValue !== undefined && detail.minOrderValue !== null) {
    return Number(detail.minOrderValue);
  }

  // Fallback to default
  return DEFAULT_MIN_MARGIN_USDT;
}

// Compute desired trade margin: 15% of available balance, but not below min margin
function getTradeMargin(symbol) {
  const minMargin = getMinMargin(symbol);
  if (!balanceReady || available_balance === null || available_balance <= 0) {
    return minMargin;
  }
  const target = available_balance * 0.35;
  const margin = Math.max(minMargin, target);
  return margin;
}

// Round to specific scale
function roundToScale(value, scale) {
  return Number(parseFloat(value).toFixed(scale));
}

// Adjust volume
function adjustVol(vol, scale) {
  if (scale === 0) return Math.floor(vol);
  return roundToScale(vol, scale);
}

// Calculate volume for order placement
function calculateVol(symbol, margin, price, leverage) {
  const contractSize = contract_sizes[symbol];
  if (!contractSize) throw new Error(`Contract size for ${symbol} not found.`);
  const positionSize = margin * leverage;
  let vol = positionSize / (Number(price) * Number(contractSize));
  const [priceScale, volScale, maxVol] = getSymbolScale(symbol);
  vol = adjustVol(vol, volScale);
  if (maxVol !== null) {
    let max_vol = Number(maxVol);
    if (vol > max_vol) {
      const min_unit = volScale === 0 ? 1 : Math.pow(10, -volScale);
      vol = max_vol - min_unit;
      if (vol < min_unit) vol = min_unit;
      vol = adjustVol(vol, volScale);
    }
  }
  return vol;
}

// Cap position notional (margin * leverage) by slippage-based limit if available
function clampVolBySlippage(symbol, isLong, price, vol, leverage) {
  if (!price || price <= 0 || !vol || vol <= 0) return vol;
  const contractSize = contract_sizes[symbol];
  if (!contractSize) return vol;
  const cap = maxPositionNotional.get(symbol);
  if (!cap) {
    // No slippage cap, but still apply maxVol and balance limits
    const [ , volScale, maxVol ] = getSymbolScale(symbol);
    let cappedVol = vol;

    // Apply maxVol limit
    if (maxVol !== null && maxVol > 0) {
      const maxVolNum = Number(maxVol);
      if (cappedVol > maxVolNum) {
        cappedVol = maxVolNum;
      }
    }

    // Apply balance limit (available_balance * default coefficient * leverage)
    const BALANCE_COEFFICIENT = 0.25; // Default coefficient
    if (balanceReady && available_balance !== null && available_balance > 0 && leverage > 0) {
      const maxNotionalFromBalance = available_balance * BALANCE_COEFFICIENT * leverage;
      const maxVolFromBalance = maxNotionalFromBalance / (price * contractSize);
      if (cappedVol > maxVolFromBalance) {
        cappedVol = maxVolFromBalance;
      }
    }

    const volAdj = adjustVol(cappedVol, volScale);
    return volAdj > 0 ? volAdj : 0;
  }

  const notional = price * contractSize * vol;
  const sideCap = isLong ? (cap.longNotional || cap.worst) : (cap.shortNotional || cap.worst);
  let maxNotional = sideCap || cap.worst;
  if (!maxNotional || !Number.isFinite(maxNotional) || maxNotional <= 0) {
    // Invalid slippage cap, but still apply maxVol and balance limits
    const [ , volScale, maxVol ] = getSymbolScale(symbol);
    let cappedVol = vol;

    // Apply maxVol limit
    if (maxVol !== null && maxVol > 0) {
      const maxVolNum = Number(maxVol);
      if (cappedVol > maxVolNum) {
        cappedVol = maxVolNum;
      }
    }

    // Apply balance limit (available_balance * default coefficient * leverage)
    const BALANCE_COEFFICIENT = 0.25; // Default coefficient
    if (balanceReady && available_balance !== null && available_balance > 0 && leverage > 0) {
      const maxNotionalFromBalance = available_balance * BALANCE_COEFFICIENT * leverage;
      const maxVolFromBalance = maxNotionalFromBalance / (price * contractSize);
      if (cappedVol > maxVolFromBalance) {
        cappedVol = maxVolFromBalance;
      }
    }

    const volAdj = adjustVol(cappedVol, volScale);
    return volAdj > 0 ? volAdj : 0;
  }

  // Calculate max volume from slippage cap (use original vol if not limited by slippage)
  const isLimitedBySlippage = notional > maxNotional;
  let cappedVol = isLimitedBySlippage
    ? maxNotional / (price * contractSize)
    : vol;

  // Apply maxVol limit
  const [ , volScale, maxVol ] = getSymbolScale(symbol);
  if (maxVol !== null && maxVol > 0) {
    const maxVolNum = Number(maxVol);
    if (cappedVol > maxVolNum) {
      cappedVol = maxVolNum;
    }
  }

  // Apply balance limit (available_balance * default coefficient * leverage)
  const BALANCE_COEFFICIENT = 0.25; // Default coefficient
  if (balanceReady && available_balance !== null && available_balance > 0 && leverage > 0) {
    const maxNotionalFromBalance = available_balance * BALANCE_COEFFICIENT * leverage;
    const maxVolFromBalance = maxNotionalFromBalance / (price * contractSize);
    if (cappedVol > maxVolFromBalance) {
      cappedVol = maxVolFromBalance;
    }
  }

  const volAdj = adjustVol(cappedVol, volScale);
  return volAdj > 0 ? volAdj : 0;
}

// Get maximum leverage for symbol
function getMaxLeverage(symbol) {
  const detail = contract_details[symbol];
  if (detail && detail.maxLeverage !== null && detail.maxLeverage !== undefined) {
    return Math.min(Number(detail.maxLeverage), MAX_LEVERAGE);
  }
  // Fallback to MAX_LEVERAGE if not found in contract details
  return MAX_LEVERAGE;
}

// Fetch contract details
async function fetchContractSizesAndDetails() {
  logInfo("Fetching contract sizes and details from MEXC...");
  try {
    const response = await axios.get('https://contract.mexc.com/api/v1/contract/detail', { timeout: 15000 });
    const data = response.data;
    let zeroMaxVolCount = 0;
    let nullMaxVolCount = 0;

    for (const entry of data.data || []) {
      const symbol = entry.symbol;
      const contractSize = entry.contractSize;
      const priceScale = entry.priceScale;
      const volScale = entry.volScale;
      const rawMaxVol = entry.maxVol;
      let maxVol = rawMaxVol === null || rawMaxVol === undefined ? null : Number(rawMaxVol);

      if (symbol) {
        // Check for zero or null maxVol (ticker will be delisted soon)
        // Check both raw value and converted value to catch all cases
        const isZeroOrNull = (rawMaxVol === 0 || rawMaxVol === "0" || rawMaxVol === null || rawMaxVol === undefined ||
                              maxVol === 0 || maxVol === null || isNaN(maxVol));

        if (isZeroOrNull) {
          BLACKLISTED_SYMBOLS.add(symbol);
          if (maxVol === 0 || rawMaxVol === 0 || rawMaxVol === "0") {
            zeroMaxVolCount++;
            logInfo(`⚠️ Added ${symbol} to blacklist (maxVol=${rawMaxVol}, type=${typeof rawMaxVol} - will be delisted)`);
          } else {
            nullMaxVolCount++;
            logInfo(`⚠️ Added ${symbol} to blacklist (maxVol=${rawMaxVol}, type=${typeof rawMaxVol} - will be delisted)`);
          }
          continue; // Skip processing this symbol
        }

        // Try to extract minimum margin from various possible fields
        const minMargin = entry.minMargin || entry.minNotional || entry.minOrderValue || null;
        // Try to extract maximum leverage
        const maxLeverage = entry.maxLeverage || entry.leverage || null;

        // Use override if available, otherwise use API value
        const finalMaxVol = contractMaxVolOverrides[symbol] !== undefined
          ? contractMaxVolOverrides[symbol]
          : maxVol;

        contract_details[symbol] = {
          priceScale,
          volScale,
          contractSize,
          maxVol: finalMaxVol,
          minMargin: minMargin !== null ? Number(minMargin) : null,
          maxLeverage: maxLeverage !== null ? Number(maxLeverage) : null
        };
        contract_sizes[symbol] = Number(contractSize);
      }
    }
    logInfo(`Loaded ${Object.keys(contract_details).length} contract details`);
    if (zeroMaxVolCount > 0 || nullMaxVolCount > 0) {
      logInfo(`📋 Blacklist summary: ${zeroMaxVolCount} tickers with maxVol=0, ${nullMaxVolCount} tickers with maxVol=null (total blacklisted: ${BLACKLISTED_SYMBOLS.size})`);
    } else {
      logInfo(`✅ No tickers with zero or null maxVol found`);
    }
  } catch (err) {
    logError(`Error fetching contract sizes: ${err.message}`);
  }
}

// Safe wrapper to refresh contract details (periodic/all-tickers)
async function refreshContractDetails(trigger = 'manual') {
  if (contractRefreshInProgress) {
    logInfo(`⏳ Contract detail refresh skipped (${trigger}) - already running`);
    return;
  }
  contractRefreshInProgress = true;
  try {
    await fetchContractSizesAndDetails();
  } catch (err) {
    logError(`❌ Contract detail refresh failed (${trigger}): ${err.message || err}`);
  } finally {
    contractRefreshInProgress = false;
  }
}

// Fetch initial balance using API keys
async function fetchInitialBalance() {
  logInfo("Fetching initial balance via API keys...");
  try {
    const result = await getAccountBalance();
    if (!result) {
      logWarn("Balance fetch returned null, setting default values");
      available_balance = 0;
      balanceReady = true;
    }
  } catch (err) {
    logError(`Error fetching initial balance: ${err.message}`);
    // Set default values on error
    available_balance = 0;
    balanceReady = true;
  }
}

// Save balances to file for bot
function saveBalancesToFile() {
  try {
    const BALANCE_FILE = path.join(__dirname, 'account_balances.json');
    const balances = {
      futures: balanceReady && Number.isFinite(available_balance) ? available_balance : null,
      spot: spotBalanceReady && Number.isFinite(spotAvailableBalance) ? spotAvailableBalance : null,
      lastUpdate: Date.now()
    };
    fs.writeFileSync(BALANCE_FILE, JSON.stringify(balances, null, 2));
  } catch (err) {
    logError(`Failed to save balances to file: ${err.message}`);
  }
}

// Safe wrapper to refresh balance without overlapping calls
async function refreshBalance(trigger = 'manual') {
  if (balanceRefreshInProgress) {
    logInfo(`⏳ Balance refresh skipped (${trigger}) - already running`);
    return;
  }
  balanceRefreshInProgress = true;
  const previousBalance = available_balance;
  const previousReady = balanceReady;
  try {
    logInfo(`🔄 Starting balance refresh (${trigger}) - current: ${previousBalance || 'N/A'}`);
    await fetchInitialBalance();
    if (!(balanceReady && available_balance !== null)) {
      logWarn(`⚠️ Balance refresh incomplete (${trigger}) - resetting to previous values`);
      available_balance = previousBalance;
      balanceReady = previousReady;
    } else {
      logInfo(`✅ Balance refresh completed (${trigger}) - new balance: ${available_balance}`);
      saveBalancesToFile(); // Save to file for bot
    }
  } catch (err) {
    logError(`❌ Balance refresh failed (${trigger}): ${err.message || err}`);
    // Restore previous values on error
    available_balance = previousBalance;
    balanceReady = previousReady;
  } finally {
    balanceRefreshInProgress = false;
  }
}

// Print status update
function printStatusUpdate() {
  const now = Date.now();
  const wsUpdateAgo = stats.lastWebSocketUpdate
    ? Math.floor((now - stats.lastWebSocketUpdate) / 1000)
    : null;
  const uniqueSymbols = Object.keys(tickerData).length;

  // Recalculate current max spread from all tracked symbols
  let currentMaxSpread = 0;
  let currentMaxSpreadSymbol = null;
  let currentMaxSpreadDirection = null;
  for (const [symbol, data] of Object.entries(tickerData)) {
    if (data.markPrice > 0 && data.lastPrice > 0) {
      const diff = Math.abs(data.markPrice - data.lastPrice);
      const diffPercent = diff / data.lastPrice;
      if (diffPercent > currentMaxSpread) {
        currentMaxSpread = diffPercent;
        currentMaxSpreadSymbol = symbol;
        currentMaxSpreadDirection = data.markPrice > data.lastPrice ? 'LONG' : 'SHORT';
      }
    }
  }
  stats.currentMaxSpread = currentMaxSpread;
  stats.currentMaxSpreadSymbol = currentMaxSpreadSymbol;
  stats.currentMaxSpreadDirection = currentMaxSpreadDirection;

  console.log('\n' + '='.repeat(60));
  logInfo('📊 STATUS UPDATE');
  console.log('='.repeat(60));
  logInfo(`   Batch messages received: ${stats.totalMessagesReceived}`);
  logInfo(`   Total ticker updates: ${stats.totalTickersReceived} (${stats.totalMessagesReceived > 0 ? Math.round(stats.totalTickersReceived / stats.totalMessagesReceived) : 0} per batch)`);
  logInfo(`   Unique symbols tracked: ${uniqueSymbols}`);
  logInfo(`   Orderbooks ready: ${stats.orderbooksReady}`);
  logInfo(`   Tickers processed: ${stats.totalTickersProcessed}`);
  logInfo(
    `   Opportunities found: ${stats.opportunitiesFound} (USDT: ${stats.opportunitiesUSDT}, Non-USDT: ${stats.opportunitiesNonUSDT})` +
    ` (FAIR: ${stats.opportunitiesFoundFair}, GMGN: ${stats.opportunitiesFoundGmgn}, SPOT-FUTURES: ${stats.opportunitiesFoundSpotFutures || 0})`
  );
  logInfo(`=============== Fair + GMGN ================`); // user requested separator
  if (stats.opportunitiesSkippedNoOrderbook > 0) {
    logInfo(`   Opportunities skipped (no orderbook): ${stats.opportunitiesSkippedNoOrderbook}`);
  }
  if (stats.opportunitiesSkippedDisabled > 0) {
    logInfo(`   Opportunities skipped (direction disabled): ${stats.opportunitiesSkippedDisabled}`);
  }
  if (stats.tradeExecutionsStarted > 0) {
    logInfo(`   Trade executions started: ${stats.tradeExecutionsStarted} (FAIR: ${stats.tradeExecutionsStartedFair}, GMGN: ${stats.tradeExecutionsStartedGmgn})`);
  }
  if (activeTrades.size > 0) {
    let activeFair = 0;
    let activeGmgn = 0;
    for (const t of activeTrades.values()) {
      if (t && t.strategy === 'gmgn') activeGmgn++;
      else activeFair++;
    }
    logInfo(`   Active trades: ${activeTrades.size} (FAIR: ${activeFair}, GMGN: ${activeGmgn})`);
  }
  logInfo(`   Orders placed: ${stats.ordersPlaced} (FAIR: ${stats.ordersPlacedFair}, GMGN: ${stats.ordersPlacedGmgn})`);
  if (stats.ordersFailed > 0) {
    logInfo(`   Orders failed: ${stats.ordersFailed} (FAIR: ${stats.ordersFailedFair}, GMGN: ${stats.ordersFailedGmgn})`);
    if (stats.orderFailReasons && stats.orderFailReasons.size > 0) {
      logInfo(`   Failure reasons:`);
      // Sort by count (descending) and show top reasons
      const sortedReasons = Array.from(stats.orderFailReasons.entries())
        .sort((a, b) => b[1] - a[1])
        .slice(0, 10); // Show top 10 reasons
      for (const [reason, count] of sortedReasons) {
        logInfo(`     - ${reason}: ${count}`);
      }
    }
  } else {
    logInfo(`   Orders failed: 0 (FAIR: 0, GMGN: 0)`);
  }
  logInfo(`   Threshold LONG: ${(FAIR_PRICE_THRESHOLD_LONG * 100).toFixed(2)}% ${ENABLE_LONG ? '✅ ENABLED' : '❌ DISABLED'}`);
  logInfo(`   Threshold SHORT: ${(FAIR_PRICE_THRESHOLD_SHORT * 100).toFixed(2)}% ${ENABLE_SHORT ? '✅ ENABLED' : '❌ DISABLED'}`);
  if (stats.maxSpreadFound > 0) {
    logInfo(`   Max spread found: ${(stats.maxSpreadFound * 100).toFixed(2)}% ${stats.maxSpreadDirection || ''} (${stats.maxSpreadSymbol})`);
  } else {
    logInfo(`   Max spread found: N/A`);
  }
  if (stats.currentMaxSpread > 0) {
    logInfo(`   Current max spread: ${(stats.currentMaxSpread * 100).toFixed(2)}% ${stats.currentMaxSpreadDirection || ''} (${stats.currentMaxSpreadSymbol})`);
  } else {
    logInfo(`   Current max spread: N/A`);
  }

  // Show top 5 spreads
  if (stats.topSpreads.length > 0) {
    logInfo(`   Top 5 spreads:`);
    for (let i = 0; i < stats.topSpreads.length; i++) {
      const spread = stats.topSpreads[i];
      logInfo(`     ${i + 1}. ${(spread.spread * 100).toFixed(2)}% ${spread.direction} (${spread.symbol}) [${spread.source || 'FAIR'}]`);
    }
  } else {
    logInfo(`   Top 5 spreads: N/A`);
  }

  if (wsUpdateAgo !== null) {
    logInfo(`   Last WebSocket update: ${wsUpdateAgo}s ago`);
  } else {
    logInfo(`   Last WebSocket update: waiting...`);
  }
  logInfo(`   Available balance: ${Number.isFinite(available_balance) ? available_balance.toFixed(8) : 'N/A'} USDT`);
  
  // Spot-Futures Arbitrage status
  if (ENABLE_SPOT_FUTURES_ARBITRAGE) {
    logInfo(`========== SPOT-FUTURES ARBITRAGE ==========`);
    // Count actually active orderbooks (have recent data)
    const activeOrderbooks = Object.values(spotOrderbooks).filter(ob => ob.depthTs && (Date.now() - ob.depthTs) < 60000).length;
    const spotObSource = ENABLE_SPOT_ORDERBOOK_WS ? `${Math.ceil(spotOrderbookUpdatersStarted.size / SPOT_WS_MAX_SUBSCRIPTIONS_PER_SOCKET)} WS` : 'REST bookTicker';
    const spotObAgo = spotBookTickerLastUpdate ? `${Math.floor((Date.now() - spotBookTickerLastUpdate) / 1000)}s ago` : 'waiting...';
    logInfo(`   Spot balance: ${Number.isFinite(spotAvailableBalance) ? spotAvailableBalance.toFixed(4) : 'N/A'} USDT`);
    logInfo(`   Futures balance: ${Number.isFinite(available_balance) ? available_balance.toFixed(4) : 'N/A'} USDT`);
    const nextPositionIndex = spotFuturesArbitragePositions.size;
    let nextSpotPercent;
    if (nextPositionIndex === 0) {
      nextSpotPercent = 25;
    } else if (nextPositionIndex === 1) {
      nextSpotPercent = 33.33;
    } else if (nextPositionIndex === 2) {
      nextSpotPercent = 50;
    } else {
      nextSpotPercent = 100;
    }
    const nextSpotValue = Number.isFinite(spotAvailableBalance) ? spotAvailableBalance * (nextSpotPercent / 100) : 0;
    const nextFuturesValue = Number.isFinite(available_balance) ? available_balance * 0.25 : 0;
    const nextTradeValue = Math.min(nextSpotValue, nextFuturesValue);
    logInfo(`   Next trade size: ${nextSpotPercent}% spot (${nextSpotValue.toFixed(4)} USDT) OR 25% futures (${nextFuturesValue.toFixed(4)} USDT) = ${nextTradeValue.toFixed(4)} USDT`);
    logInfo(`   Spot symbols tracked: ${spotSymbols.size}`);
    logInfo(`   Spot orderbooks: ${activeOrderbooks}/${spotOrderbookUpdatersStarted.size} active (${spotObSource}, last: ${spotObAgo})`);
    logInfo(`   Arbitrage blacklist: ${spotFuturesBlacklist.size}`);
    logInfo(`   Open arbitrage positions: ${spotFuturesArbitragePositions.size}/${SPOT_FUTURES_MAX_POSITIONS}`);

    // Deals count (spot-futures arbitrage)
    logInfo(`   Spot-futures deals: opened=${stats.spotFuturesTradesOpened || 0}, closed=${stats.spotFuturesTradesClosed || 0}`);

    // Show top 5 spot-futures spreads (moved into SPOT-FUTURES/spot section)
    if (stats.topSpotFuturesSpreads && stats.topSpotFuturesSpreads.length > 0) {
      logInfo(`   Top 5 SPOT-FUTURES spreads:`);
      for (let i = 0; i < stats.topSpotFuturesSpreads.length; i++) {
        const x = stats.topSpotFuturesSpreads[i];
        logInfo(`     ${i + 1}. ${(x.spread * 100).toFixed(2)}% (${x.spotSymbol} vs ${x.futuresSymbol})`);
      }
    } else {
      logInfo(`   Top 5 SPOT-FUTURES spreads: N/A`);
    }
    
  }

  // Open trades details must be printed before PnL summary
  logInfo(`=============================================`);
  logInfo(`   OPEN TRADES (DETAILS)`);

  let anyOpen = false;
  let sumPnlFair = 0;
  let sumPnlFairLong = 0;
  let sumPnlFairShort = 0;
  let countFairLongOpen = 0;
  let countFairShortOpen = 0;
  let sumPnlGmgn = 0;
  let sumPnlGmgnLong = 0;
  let sumPnlGmgnShort = 0;
  let countGmgnLongOpen = 0;
  let countGmgnShortOpen = 0;
  let sumPnlSpotFutures = 0;
  let countSpotSpreadOpen = 0;

  // FAIR / GMGN (futures)
  if (activeTrades.size > 0) {
    const fairTrades = [];
    const gmgnTrades = [];
    for (const t of activeTrades.values()) {
      if (!t) continue;
      if (t.strategy === 'gmgn') gmgnTrades.push(t);
      else fairTrades.push(t);
    }

    const showTradeList = (label, list) => {
      if (list.length === 0) return;
      anyOpen = true;
      logInfo(`   --- ${label} ---`);
      list.sort((a, b) => String(a.symbol).localeCompare(String(b.symbol)));
      for (const trade of list) {
        const symbol = trade.symbol;
        const ob = orderbooks[symbol];
        const lastPrice = tickerData[symbol]?.lastPrice || 0;
        const exitPrice = computeExitPrice(trade, ob, lastPrice);
        const pnlPercent = computePnlPercent(trade, exitPrice);
        const pnlUSDT = computeUnrealizedPnlUSDT(trade, exitPrice);
        const isLong = trade.isLong === true;
        if (label === 'FAIR') {
          if (isLong) countFairLongOpen += 1;
          else countFairShortOpen += 1;
        } else if (label === 'GMGN') {
          if (isLong) countGmgnLongOpen += 1;
          else countGmgnShortOpen += 1;
        }
        if (pnlUSDT !== null) {
          if (label === 'GMGN') {
            sumPnlGmgn += pnlUSDT;
            if (isLong) sumPnlGmgnLong += pnlUSDT;
            else sumPnlGmgnShort += pnlUSDT;
          } else {
            sumPnlFair += pnlUSDT;
            if (isLong) sumPnlFairLong += pnlUSDT;
            else sumPnlFairShort += pnlUSDT;
          }
        }
        const elapsedMin = ((now - (trade.entryTime || now)) / 1000 / 60).toFixed(1);
        const vol = Number(trade.remainingVol ?? trade.openVol);
        const pnlUSDTText = pnlUSDT === null ? 'N/A' : `${pnlUSDT.toFixed(4)} USDT`;
        logInfo(
          `     ${symbol}: ${trade.direction} entry ${Number(trade.entryPrice).toFixed(8)} → ${Number(exitPrice || trade.entryPrice).toFixed(8)}, ` +
          `vol=${Number.isFinite(vol) ? vol : 'N/A'}, PnL: ${pnlUSDTText} (${(pnlPercent * 100).toFixed(2)}%), ${elapsedMin}min`
        );
      }
      const sum = label === 'GMGN' ? sumPnlGmgn : sumPnlFair;
      const realized = label === 'GMGN' ? (stats.realizedPnlGmgn || 0) : (stats.realizedPnlFair || 0);
      logInfo(`   ${label} unrealized PnL (sum): ${sum.toFixed(4)} USDT, realized: ${realized.toFixed(4)} USDT`);
    };

    showTradeList('FAIR', fairTrades);
    showTradeList('GMGN', gmgnTrades);
  }

  // SPOT-FUTURES (paired)
  if (spotFuturesArbitragePositions.size > 0) {
    const openArbs = [];
    for (const pos of spotFuturesArbitragePositions.values()) {
      if (pos && pos.status === 'open') openArbs.push(pos);
    }
    if (openArbs.length > 0) {
      anyOpen = true;
      countSpotSpreadOpen = openArbs.length;
      logInfo(`   --- SPOT-FUTURES ---`);
      openArbs.sort((a, b) => String(a.spotSymbol).localeCompare(String(b.spotSymbol)));
      for (const pos of openArbs) {
        const spotOb = spotOrderbooks[pos.spotSymbol];
        const futuresOb = orderbooks[pos.futuresSymbol];
        const spotBid = spotOb?.best_bid || pos.spotEntryPrice;
        const futuresAsk = futuresOb?.best_sell || pos.futuresEntryPrice;
        const currentSpread = (futuresAsk - spotBid) / spotBid;

        const spotPnl = (spotBid - pos.spotEntryPrice) * pos.spotQty;
        const futuresPnl = (pos.futuresEntryPrice - futuresAsk) * pos.futuresVol * (contract_sizes[pos.futuresSymbol] || 1);
        const totalPnl = spotPnl + futuresPnl;
        if (Number.isFinite(totalPnl)) sumPnlSpotFutures += totalPnl;
        const pnlPercent = totalPnl / (pos.spotEntryPrice * pos.spotQty);
        const elapsed = ((now - pos.openTime) / 1000 / 60).toFixed(1);

        logInfo(
          `     ${pos.spotSymbol}: spread ${(pos.openSpread * 100).toFixed(2)}% → ${(currentSpread * 100).toFixed(2)}%, ` +
          `PnL: ${totalPnl.toFixed(4)} USDT (${(pnlPercent * 100).toFixed(2)}%), ${elapsed}min`
        );
      }
      logInfo(`   SPOT-FUTURES unrealized PnL (sum): ${sumPnlSpotFutures.toFixed(4)} USDT, realized: ${(stats.realizedPnlSpotFutures || 0).toFixed(4)} USDT`);
    }
  }

  if (!anyOpen) {
    logInfo(`   No open trades.`);
  }

  // PnL summary across all trade types (realized + unrealized)
  logInfo(`=============================================`);
  logInfo(`   PNL SUMMARY (realized + unrealized)`);
  const realizedFairShort = Number(stats.realizedPnlFairShort || 0);
  const realizedFairLong = Number(stats.realizedPnlFairLong || 0);
  const realizedCountFairShort = Number(stats.realizedCountFairShort || 0);
  const realizedCountFairLong = Number(stats.realizedCountFairLong || 0);
  const realizedGmgnShort = Number(stats.realizedPnlGmgnShort || 0);
  const realizedGmgnLong = Number(stats.realizedPnlGmgnLong || 0);
  const realizedCountGmgnShort = Number(stats.realizedCountGmgnShort || 0);
  const realizedCountGmgnLong = Number(stats.realizedCountGmgnLong || 0);
  const realizedSpotSpread = Number(stats.realizedPnlSpotFutures || 0);
  const realizedCountSpotSpread = Number(stats.realizedCountSpotFutures || 0);

  const pnlFairShort = sumPnlFairShort + realizedFairShort;
  const pnlFairLong = sumPnlFairLong + realizedFairLong;
  const countFairShortTotal = countFairShortOpen + realizedCountFairShort;
  const countFairLongTotal = countFairLongOpen + realizedCountFairLong;
  const pnlGmgnShort = sumPnlGmgnShort + realizedGmgnShort;
  const pnlGmgnLong = sumPnlGmgnLong + realizedGmgnLong;
  const countGmgnShortTotal = countGmgnShortOpen + realizedCountGmgnShort;
  const countGmgnLongTotal = countGmgnLongOpen + realizedCountGmgnLong;
  const pnlSpotSpread = sumPnlSpotFutures + realizedSpotSpread;
  const countSpotSpreadTotal = countSpotSpreadOpen + realizedCountSpotSpread;
  const totalPnl = pnlFairShort + pnlFairLong + pnlGmgnShort + pnlGmgnLong + pnlSpotSpread;
  const totalCount = countFairShortTotal + countFairLongTotal + countGmgnShortTotal + countGmgnLongTotal + countSpotSpreadTotal;

  logInfo(`   ${countFairShortTotal}x Fair Short PnL: ${pnlFairShort.toFixed(4)} USDT, ${countFairLongTotal}x Fair Long PnL: ${pnlFairLong.toFixed(4)} USDT`);
  logInfo(`   ${countGmgnShortTotal}x GMGN Short PnL: ${pnlGmgnShort.toFixed(4)} USDT, ${countGmgnLongTotal}x GMGN Long PnL: ${pnlGmgnLong.toFixed(4)} USDT`);
  logInfo(`   ${countSpotSpreadTotal}x Spot Spread PnL: ${pnlSpotSpread.toFixed(4)} USDT`);
  logInfo(`   ${totalCount}x Total PnL: ${totalPnl.toFixed(4)} USDT`);

  console.log('='.repeat(60) + '\n');

  stats.lastStatusUpdate = now;
}

// ---------------------- Unified position opening (shared by FAIR + GMGN) ----------
async function openTradeFromSignal(params = {}) {
  const {
    symbol,
    strategy = 'fair',
    isLong,
    entryPrice,
    referencePrice = null,
    initialSpread = null,
    openType = null, // Will be set based on strategy if not provided
    leverageOverride = null,
    marginOverride = null,
    cooldownMs = LAST_CLOSE_DIRECTION_COOLDOWN_MS,
    applySlippageCap = true,
    maxDrawdownPercent = null,
    takeProfitPercentForOrder = null,
    skipTpLimitPlacement = false
  } = params;
  
  // Set openType based on strategy if not explicitly provided
  // CRITICAL: openType: 1 = ISOLATED, openType: 2 = CROSS
  // GMGN MUST use cross (2), FAIR uses isolated (1)
  let finalOpenType;
  if (openType !== null && openType !== undefined && openType !== 0) {
    finalOpenType = Number(openType);
  } else {
    // Default based on strategy
    finalOpenType = (strategy === 'gmgn' ? 2 : 1); // GMGN: cross (2), FAIR: isolated (1)
  }
  
  // Force GMGN to use cross (2) - override any incorrect value
  if (strategy === 'gmgn' && finalOpenType !== 2) {
    logWarn(`⚠️ WARNING: GMGN strategy should use cross (2), but got openType=${finalOpenType}. Forcing to 2.`);
    finalOpenType = 2;
  }
  
  // Force FAIR to use isolated (1) - override any incorrect value
  if (strategy === 'fair' && finalOpenType !== 1) {
    logWarn(`⚠️ WARNING: FAIR strategy should use isolated (1), but got openType=${finalOpenType}. Forcing to 1.`);
    finalOpenType = 1;
  }

  if (!symbol) return;
  if (!balanceReady) {
    logWarn(`[${strategy}] Balance not ready. Not opening position.`);
    return;
  }
  if (!entryPrice || entryPrice <= 0) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'invalid entry price', { entryPrice }, 30000);
    }
    return;
  }

  // Direction gating (reuse global toggles)
  if (isLong && !ENABLE_LONG) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'long direction disabled', null, 30000);
    }
    return;
  }
  if (!isLong && !ENABLE_SHORT) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'short direction disabled', null, 30000);
    }
    return;
  }

  // Safety: only USDT pairs are traded
  let isUSDT = symbolIsUSDT[symbol];
  if (isUSDT === undefined) {
    isUSDT = symbol.endsWith('_USDT');
    symbolIsUSDT[symbol] = isUSDT;
  }
  if (!isUSDT) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'not a USDT futures pair', null, 60000);
    }
    return;
  }

  // Hard blacklist
  if (BLACKLISTED_SYMBOLS.has(symbol)) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'hard blacklist');
    }
    return;
  }

  // GMGN-specific blocks (extra parity checks)
  if (strategy === 'gmgn') {
    if (isTickerBlacklisted(symbol)) {
      logGmgnSkip(symbol, 'ticker blacklist');
      return;
    }
    if (ENABLE_DEPOSIT_WITHDRAW_CHECK && isDepositWithdrawBlacklisted(symbol)) {
      logGmgnSkip(symbol, 'deposit/withdraw blacklist');
      return;
    }
  }

  // Avoid duplicates: already tracking or in-flight
  if (getActiveTrade(symbol)) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'active trade already exists');
    }
    return;
  }
  if (inFlightOpens.has(symbol)) {
    if (strategy === 'gmgn') {
      logGmgnSkip(symbol, 'open order is in-flight');
    }
    return;
  }

  // If there is already a live position on this symbol (manual or other session), skip immediately
  const existingPosMap = symbolPositions.get(symbol);
  const hasLivePosExisting = existingPosMap && [...existingPosMap.values()].some(p => p.holdVol > 0 && !closed_positions.has(p.positionId || ""));
  if (hasLivePosExisting) {
    manualPositionHold.add(symbol);
    logWarn(`🚫 ${symbol}: detected existing open position before order placement, skipping this symbol until position is closed.`);
    return;
  }

  // Contract details required for sizing
  if (!contract_details[symbol]) {
    logWarn(`⚠️ Contract details not available for ${symbol}, skipping...`);
    return;
  }

  // Mark in-flight early (prevents races; also contributes to the shared MAX_OPEN_POSITIONS counter).
  markInFlight(symbol);
  let keepInFlight = false;

  try {
    // Enforce global max open positions (include this in-flight)
    const totalOpenPositions = getTotalOpenPositions();
    const inFlightTotal = getInFlightTotal();
    if ((totalOpenPositions + inFlightTotal) > MAX_OPEN_POSITIONS) {
      logInfo(`⚠️ Maximum open positions limit reached (${totalOpenPositions}+inflight:${inFlightTotal}/${MAX_OPEN_POSITIONS}). Skipping new order for ${symbol}.`);
      if (strategy === 'gmgn') {
        logGmgnSkip(symbol, 'max open positions limit reached', {
          totalOpenPositions,
          inFlightTotal,
          maxOpenPositions: MAX_OPEN_POSITIONS
        }, 10000);
      }
      return;
    }

    // Cooldown after a loss in the same direction until price starts moving our way
    const lastCloseTs = getLastCloseTimestamp(symbol, isLong);
    if (lastCloseTs && (Date.now() - lastCloseTs) < cooldownMs) {
      if (!hasPriceMovedInDirection(symbol, isLong)) {
        const secondsAgo = ((Date.now() - lastCloseTs) / 1000).toFixed(1);
        const directionLabel = isLong ? 'LONG' : 'SHORT';
        logInfo(`[${symbol}] ${directionLabel} closed ${secondsAgo}s ago. Waiting for ${directionLabel === 'LONG' ? 'upward' : 'downward'} move over last ${Math.round(PRICE_TREND_WINDOW_MS/1000)}s before re-entering.`);
        if (strategy === 'gmgn') {
          logGmgnSkip(symbol, 'direction cooldown active', {
            direction: directionLabel,
            secondsAgo: Number(secondsAgo)
          }, 10000);
        }
        return;
      }
    }
    
    // GMGN: Проверка кд для двух минусов подряд с убытком > 6$
    if (strategy === 'gmgn' && isGmgnConsecutiveLossCooldownActive(symbol, isLong)) {
      const lastCloseTsGmgn = getLastCloseTimestamp(symbol, isLong);
      const secondsAgo = ((Date.now() - lastCloseTsGmgn) / 1000).toFixed(1);
      const directionLabel = isLong ? 'LONG' : 'SHORT';
      logInfo(`[GMGN] ${symbol} ${directionLabel}: КД 60 сек после двух минусов подряд (${secondsAgo}s ago).`);
      return;
    }

    const direction = isLong ? 'LONG' : 'SHORT';
    const side = isLong ? 1 : 3; // 1=open long, 3=open short

    // Leverage & margin per strategy
    let leverage = leverageOverride !== null && leverageOverride !== undefined
      ? Number(leverageOverride)
      : getMaxLeverage(symbol);
    if (!Number.isFinite(leverage) || leverage <= 0) {
      leverage = getMaxLeverage(symbol);
    }

    let margin = marginOverride !== null && marginOverride !== undefined
      ? Number(marginOverride)
      : getTradeMargin(symbol);
    if (!Number.isFinite(margin) || margin <= 0) {
      logWarn(`⚠️ Invalid margin computed for ${symbol}, skipping...`);
      return;
    }

    const [priceScale, volScale, maxVol] = getSymbolScale(symbol);

    // Skip symbols with maxVol=0 (cannot be traded at this leverage)
    if (maxVol !== null && Number(maxVol) === 0) {
      logWarn(`🚫 ${symbol}: maxVol=0 - symbol cannot be traded at this leverage. Skipping order.`);
      return;
    }

    let vol;
    try {
      const volRaw = calculateVol(symbol, margin, entryPrice, leverage);
      vol = applySlippageCap ? clampVolBySlippage(symbol, isLong, entryPrice, volRaw, leverage) : volRaw;
      vol = adjustVol(vol, volScale);
    } catch (e) {
      logError(`Failed to calculate volume for ${symbol}: ${e.message}`);
      return;
    }

    if (!Number.isFinite(vol) || vol <= 0) {
      logWarn(`⚠️ Calculated volume is 0 or invalid for ${symbol}, skipping...`);
      return;
    }

    // Create market order
    // CRITICAL: Ensure openType is explicitly set as number (1=isolated, 2=cross)
    // GMGN strategy MUST use cross (2), FAIR strategy uses isolated (1)
    const order = {
      symbol,
      side,
      openType: Number(finalOpenType), // Force to number: 2=cross for GMGN, 1=isolated for FAIR
      type: "5",
      vol,
      leverage,
      priceProtect: "0",
      ts: Date.now(),
      marketCeiling: 'false'
    };

    // Optional: attach stopLoss/takeProfit to open order (used by GMGN TP script)
    // Use proper stop-loss percentages: 5% for LONG, 50% for SHORT
    const stopLossPercent = isLong ? (LONG_STOP_LOSS_PERCENT / 100) : (GLOBAL_STOP_LOSS_PERCENT / 100);
    if ((stopLossPercent > 0) || (Number.isFinite(takeProfitPercentForOrder) && takeProfitPercentForOrder > 0)) {
      const chosenPrice = roundToScale(entryPrice, priceScale);
      if (stopLossPercent > 0) {
        const sl = isLong ? chosenPrice * (1 - stopLossPercent) : chosenPrice * (1 + stopLossPercent);
        order.stopLossPrice = String(roundToScale(sl, priceScale));
      }
      if (Number.isFinite(takeProfitPercentForOrder) && takeProfitPercentForOrder > 0) {
        const tp = isLong ? chosenPrice * (1 + takeProfitPercentForOrder) : chosenPrice * (1 - takeProfitPercentForOrder);
        order.takeProfitPrice = String(roundToScale(tp, priceScale));
      }
    }
    
    // Log order details for debugging - CRITICAL for GMGN cross margin verification
    logInfo(`   🔍 Order details: symbol=${symbol}, side=${side}, openType=${order.openType} (${order.openType === 2 ? 'CROSS' : order.openType === 1 ? 'ISOLATED' : 'UNKNOWN'}), strategy=${strategy}, finalOpenType=${finalOpenType}`);

    const tradeContext = {
      strategy,
      direction,
      isLong,
      entryPrice,
      leverage,
      volume: vol,
      initialSpread: Number(initialSpread) || 0,
      openType: finalOpenType, // Use finalOpenType instead of openType
      referencePrice: Number(referencePrice) || null,
      tpOrdersPlaced: skipTpLimitPlacement ? false : false // For GMGN (skipTpLimitPlacement=true), TP will be placed in handlePositionUpdate, so keep false initially
    };

    logInfo(`   ▶️ Opening ${strategy.toUpperCase()} ${direction} ${symbol}: price=${entryPrice.toFixed(8)} vol=${vol} lev=${leverage}x openType=${finalOpenType}`);

    let resp = await placeOrder(MEXC_KEY, order);

    // Check for delisting error (message contains "delisted") - automatically remove token from tokens.json
    // Note: We check message text, not just code 8823, as code 8823 might be used for other errors
    const isDelisted = resp && !resp.success && resp.message && typeof resp.message === 'string' && 
      resp.message.toLowerCase().includes('delisted');
    if (isDelisted) {
      logError(`🚫 Token ${symbol} will be delisted (detected in error message). Automatically removing from tokens.json.`);
      
      // Remove token from tokens.json
      try {
        const tokensPath = path.join(__dirname, 'tokens.json');
        if (fs.existsSync(tokensPath)) {
          const raw = fs.readFileSync(tokensPath, 'utf8');
          const tokens = JSON.parse(raw);
          const mexcName = symbol.toUpperCase();
          const index = tokens.findIndex(t => t.mexc_name === mexcName);
          if (index !== -1) {
            tokens.splice(index, 1);
            fs.writeFileSync(tokensPath, JSON.stringify(tokens, null, 2));
            logInfo(`✅ Removed ${mexcName} from tokens.json (delisted)`);
            
            // Reload GMGN configs to remove delisted token
            try {
              gmgnTokenConfigs = loadGmgnTokenConfigsFromFile();
              gmgnConfigBySymbol.clear();
              for (const tokenCfg of gmgnTokenConfigs) {
                gmgnConfigBySymbol.set(tokenCfg.mexc_name, tokenCfg);
              }
            } catch (err) {
              logWarn(`Failed to reload GMGN configs after removing delisted token: ${err.message}`);
            }
          }
        }
      } catch (err) {
        logError(`Failed to remove delisted token ${symbol} from tokens.json: ${err.message}`);
      }
      
      // Add to blacklist to prevent further attempts
      BLACKLISTED_SYMBOLS.add(symbol);
      stats.ordersFailed++;
      if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
      return;
    }

    // Handle maxVol error (code 8819) - block symbol if maxVol=0
    if (resp && !resp.success && resp.code === 8819) {
      const forcedCap = Number(resp._extend?.amount);
      const detail = contract_details[symbol];

      if (!Number.isFinite(forcedCap) || forcedCap <= 0) {
        logWarn(`🚫 ${symbol}: Received maxVol=0 from error 8819 - BLOCKING symbol from trading!`);
        contractMaxVolOverrides[symbol] = 0;
        contract_details[symbol] = {
          ...detail,
          priceScale: detail.priceScale ?? priceScale,
          volScale: detail.volScale ?? volScale,
          maxVol: 0
        };
        BLACKLISTED_SYMBOLS.add(symbol);
        stats.ordersFailed++;
        if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
        const reason = `maxVol=0 (code 8819)`;
        stats.orderFailReasons.set(reason, (stats.orderFailReasons.get(reason) || 0) + 1);
        return;
      }

      // Retry with adjusted volume (cap)
      const currentMax = detail.maxVol;
      const newCap = currentMax != null ? Math.min(currentMax, forcedCap) : forcedCap;
      contractMaxVolOverrides[symbol] = newCap;
      contract_details[symbol] = {
        ...detail,
        priceScale: detail.priceScale ?? priceScale,
        volScale: detail.volScale ?? volScale,
        maxVol: newCap
      };

      const minVolumeStep = volScale === 0 ? 1 : Math.pow(10, -volScale);
      const adjustedVol = Math.min(vol, newCap);
      if (adjustedVol < minVolumeStep) {
        logWarn(`🚫 ${symbol}: leverage cap ${forcedCap} below minimum volume step ${minVolumeStep}. BLOCKING symbol!`);
        contractMaxVolOverrides[symbol] = 0;
        contract_details[symbol] = {
          ...detail,
          priceScale: detail.priceScale ?? priceScale,
          volScale: detail.volScale ?? volScale,
          maxVol: 0
        };
        BLACKLISTED_SYMBOLS.add(symbol);
        stats.ordersFailed++;
        if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
        const reason = `leverage cap below min step (code 8819)`;
        stats.orderFailReasons.set(reason, (stats.orderFailReasons.get(reason) || 0) + 1);
        return;
      }

      logWarn(`⚠️ ${symbol} capped at ${forcedCap} contracts. Retrying with vol=${adjustedVol}.`);
      order.vol = adjustedVol;
      tradeContext.volume = adjustedVol;
      resp = await placeOrder(MEXC_KEY, order);
    }

    // Handle leverage error (code 2006) - retry with correct leverage from error response
    if (resp && !resp.success && resp.code === 2006 && resp._extend && resp._extend.max) {
      const correctLeverage = Math.min(Number(resp._extend.max), MAX_LEVERAGE);
      logWarn(`⚠️ Leverage ${leverage}x too high for ${symbol}. Retrying with ${correctLeverage}x from API error response.`);

      if (contract_details[symbol]) {
        contract_details[symbol].maxLeverage = correctLeverage;
      }

      try {
        vol = calculateVol(symbol, margin, entryPrice, correctLeverage);
        vol = applySlippageCap ? clampVolBySlippage(symbol, isLong, entryPrice, vol, correctLeverage) : vol;
        vol = adjustVol(vol, volScale);
        if (!Number.isFinite(vol) || vol <= 0) {
          logError(`❌ Calculated volume is 0 or invalid for ${symbol} with leverage ${correctLeverage}x`);
          stats.ordersFailed++;
          if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
          const reason = `calculated volume is 0 (leverage ${correctLeverage}x)`;
          stats.orderFailReasons.set(reason, (stats.orderFailReasons.get(reason) || 0) + 1);
          return;
        }

        order.leverage = correctLeverage;
        order.vol = vol;
        tradeContext.leverage = correctLeverage;
        tradeContext.volume = vol;

        logInfo(`   Retrying with leverage: ${correctLeverage}x, vol=${vol}`);
        resp = await placeOrder(MEXC_KEY, order);
      } catch (e) {
        logError(`Failed to recalculate volume for ${symbol}: ${e.message}`);
        stats.ordersFailed++;
        if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
        const reason = `failed to recalculate volume: ${e.message}`;
        stats.orderFailReasons.set(reason, (stats.orderFailReasons.get(reason) || 0) + 1);
        return;
      }
    }

    if (resp && resp.success) {
      stats.ordersPlaced++;
      if (strategy === 'gmgn') {
        stats.ordersPlacedGmgn++;
        logInfo(`✅ Order placed successfully (GMGN) for ${symbol}!`);
      } else {
        stats.ordersPlacedFair++;
        logInfo(`✅ Order placed successfully (FAIR) for ${symbol}!`);
      }
      logInfo(`   Response: ${JSON.stringify(resp)}`);
      lastOrderTime[symbol] = Date.now();
      keepInFlight = true;
      registerActiveTrade(symbol, tradeContext);
      
      logInfo(`   ⏳ Waiting for position confirmation via WebSocket...`);
      return;
    }

    // Failure path
    const handledCode = resp && (resp.code === 8819 || resp.code === 2006);
    if (!handledCode) {
      stats.ordersFailed++;
      if (strategy === 'gmgn') stats.ordersFailedGmgn++; else stats.ordersFailedFair++;
      let reason = 'unknown error';
      if (resp && resp.code) {
        reason = `API error ${resp.code}`;
        if (resp.message) reason += `: ${resp.message}`;
      } else if (resp && resp.message) {
        reason = resp.message;
      } else if (!resp) {
        reason = 'no response from API';
      }
      stats.orderFailReasons.set(reason, (stats.orderFailReasons.get(reason) || 0) + 1);
    }
    logError(`❌ Failed to place order for ${symbol}: ${JSON.stringify(resp)}`);

    await ensureManualHoldIfLive(symbol, 800);
    if (resp && resp.code === 8819) {
      manualPositionHold.add(symbol);
      manualHoldUntil.set(symbol, Date.now() + MANUAL_HOLD_8819_MS);
      logWarn(`🚫 ${symbol}: received 8819 (max contracts reached), holding symbol for ${MANUAL_HOLD_8819_MS/1000}s to avoid retries.`);
    }
  } finally {
    if (!keepInFlight) {
      clearInFlight(symbol);
    }
  }
}

// Process ticker and check for trading opportunity
async function processTicker(symbol, markPrice, lastPrice) {
  // Skip blacklisted symbols early
  if (BLACKLISTED_SYMBOLS.has(symbol)) {
    return;
  }

  // Skip symbols with manual/open positions detected earlier
  const manualHold = manualPositionHold.has(symbol);
  if (manualHold) {
    const nowTs = Date.now();
    const holdUntil = manualHoldUntil.get(symbol) || 0;
    const posMap = symbolPositions.get(symbol);
    const hasLivePos = posMap && [...posMap.values()].some(p => p.holdVol > 0 && !closed_positions.has(p.positionId || ""));
    if (hasLivePos) return;
    if (holdUntil && nowTs < holdUntil) return;
    manualPositionHold.delete(symbol);
    manualHoldUntil.delete(symbol);
  }

  if (!markPrice || markPrice <= 0) {
    return;
  }

  const nowTs = Date.now();
  stats.totalTickersProcessed++;

  // Cache & detect if this is a USDT pair (only USDT pairs are traded)
  let isUSDT = symbolIsUSDT[symbol];
  if (isUSDT === undefined) {
    isUSDT = symbol.endsWith('_USDT');
    symbolIsUSDT[symbol] = isUSDT;
  }

  // Determine price source (orderbook for tradable pairs, ticker fallback for tracking-only pairs)
  const ob = orderbooks[symbol];
  const obFresh = isOrderbookFresh(ob, nowTs);
  if (ob && !obFresh) {
    updateOrderbookReadyState(symbol, false);
  }
  let currentPrice = null;
  let isLong = false;
  let priceSource = 'ticker last price';

  if (isUSDT) {
    if (ob && ob.best_buy && ob.best_sell && obFresh) {
      // Use orderbook prices for accurate entry prices
      // LONG: Fair price > ask -> buy at ask (expecting price to converge to higher fair price)
      // SHORT: Fair price < bid -> sell at bid (expecting price to converge to lower fair price)
      if (markPrice > ob.best_sell) {
        // Fair price is higher than ask -> go LONG (buy at ask, profit when price rises to fair)
        isLong = true;
        currentPrice = ob.best_sell;
        priceSource = 'ask (orderbook)';
      } else if (markPrice < ob.best_buy) {
        // Fair price is lower than bid -> go SHORT (sell at bid, profit when price falls to fair)
        isLong = false;
        currentPrice = ob.best_buy;
        priceSource = 'bid (orderbook)';
      } else {
        // Fair price is between bid and ask, no clear arbitrage opportunity
        await manageOpenTrade(symbol, markPrice, ob, lastPrice, nowTs);
        return;
      }
    } else {
      // Orderbook not available yet - check if this would be an opportunity using lastPrice
      // Only count as skipped if it would pass threshold (potential opportunity missed)
      if (lastPrice && lastPrice > 0) {
        const estimatedDiff = Math.abs(markPrice - lastPrice);
        const estimatedDiffPercent = estimatedDiff / lastPrice;
        // Check against both thresholds to see if this would be an opportunity
        const wouldBeLong = markPrice > lastPrice;
        const threshold = wouldBeLong ? FAIR_PRICE_THRESHOLD_LONG : FAIR_PRICE_THRESHOLD_SHORT;
        const enabled = wouldBeLong ? ENABLE_LONG : ENABLE_SHORT;
        if (estimatedDiffPercent >= threshold) {
          // This would be an opportunity if orderbook was available
          stats.opportunitiesSkippedNoOrderbook++;
          if (!enabled) {
            stats.opportunitiesSkippedDisabled++;
          }
          if (stats.opportunitiesSkippedNoOrderbook % 100 === 0) {
            logInfo(`   📉 Orderbook not ready for ${symbol}, potential opportunity missed (estimated spread: ${(estimatedDiffPercent * 100).toFixed(2)}%). Total skipped: ${stats.opportunitiesSkippedNoOrderbook}`);
          }
          if (!enabled && (stats.opportunitiesSkippedDisabled <= 5 || stats.opportunitiesSkippedDisabled % 50 === 0)) {
            logInfo(`   ⚠️ ${wouldBeLong ? 'LONG' : 'SHORT'} trades disabled. Opportunity muted while orderbook unavailable.`);
          }
        }
      }
      await manageOpenTrade(symbol, markPrice, obFresh ? ob : null, lastPrice, nowTs);
      return; // Skip trading without proper bid/ask prices
    }
  } else {
    // For non-USDT pairs we still track opportunities using ticker last price
    if (!lastPrice || lastPrice <= 0) {
      return;
    }
    currentPrice = lastPrice;
    isLong = markPrice > lastPrice;
  }

  await manageOpenTrade(symbol, markPrice, obFresh ? ob : null, lastPrice, nowTs);

  // Calculate difference percentage
  const diff = Math.abs(markPrice - currentPrice);
  const diffPercent = diff / currentPrice;

  // Get threshold and enabled status based on direction
  const threshold = isLong ? FAIR_PRICE_THRESHOLD_LONG : FAIR_PRICE_THRESHOLD_SHORT;
  const enabled = isLong ? ENABLE_LONG : ENABLE_SHORT;

  // Track maximum spread found (all-time)
  if (diffPercent > stats.maxSpreadFound) {
    stats.maxSpreadFound = diffPercent;
    stats.maxSpreadSymbol = symbol;
    stats.maxSpreadDirection = isLong ? 'LONG' : 'SHORT';
  }

  // Track current maximum spread (among currently tracked symbols)
  if (diffPercent > stats.currentMaxSpread) {
    stats.currentMaxSpread = diffPercent;
    stats.currentMaxSpreadSymbol = symbol;
    stats.currentMaxSpreadDirection = isLong ? 'LONG' : 'SHORT';
  }

  // Update top 5 spreads (FAIR)
  updateTopSpreads(symbol, diffPercent, (isLong ? 'LONG' : 'SHORT'), 'FAIR');

  // Check threshold BEFORE counting opportunities
  if (diffPercent < threshold) {
    return; // Difference is less than threshold
  }

  // Count opportunities that passed threshold (only USDT pairs are actually tradeable)
  stats.opportunitiesFound++;
  stats.opportunitiesFoundFair++;
  if (isUSDT) {
    stats.opportunitiesUSDT++;
  } else {
    stats.opportunitiesNonUSDT++;
  }

  // Check if trading is enabled for this direction
  if (!enabled) {
    stats.opportunitiesSkippedDisabled++;
    if (stats.opportunitiesSkippedDisabled <= 5 || stats.opportunitiesSkippedDisabled % 50 === 0) {
      logInfo(`   ⚠️ ${isLong ? 'LONG' : 'SHORT'} trades disabled. Opportunity skipped at ${(diffPercent * 100).toFixed(2)}% spread.`);
    }
    return; // Trading disabled for this direction
  }

  // Block symbol for BOTH strategies if there is already an active trade or an in-flight open.
  // Important: this is placed AFTER manageOpenTrade() so open positions are still managed/closed.
  if (getActiveTrade(symbol)) return;
  if (inFlightOpens.has(symbol)) return;
  if (flagManualHoldIfLive(symbol)) return;

  // Determine direction and side
  // LONG: Fair price above current executable price -> buy
  // SHORT: Fair price below current executable price -> sell
  const direction = isLong ? 'LONG' : 'SHORT';
  const side = isLong ? 1 : 3; // 1 = LONG (buy), 3 = SHORT (sell)
  const directionDetail = isUSDT
    ? (isLong ? 'Fair price > ask, buying at ask' : 'Fair price < bid, selling at bid')
    : (isLong ? 'Fair price > ticker price' : 'Fair price < ticker price');

  logInfo(`   ✅ Threshold passed: ${(diffPercent * 100).toFixed(2)}% >= ${(threshold * 100).toFixed(2)}%`);

  // Always log trading opportunities for all pairs
  const tradeStatus = isUSDT ? '✅ TRADABLE' : '⚠️ TRACKING ONLY (not USDT)';
  logInfo(`\n🎯 Trading opportunity detected for ${symbol} [${tradeStatus}]:`);
  logInfo(`   Mark Price (Fair): ${markPrice.toFixed(8)}`);
  logInfo(`   Market Price: ${currentPrice.toFixed(8)} (${priceSource})`);
  logInfo(`   Spread: ${(diffPercent * 100).toFixed(2)}% (threshold: ${(threshold * 100).toFixed(2)}%)`);
  logInfo(`   Direction: ${direction} (${directionDetail})`);
  logInfo(`   Starting trade execution checks...`);

  // Only trade USDT pairs
  if (!isUSDT) {
    logInfo(`   ⚠️ Skipping trade - only USDT pairs are traded`);
    return;
  }

  logInfo(`   ✅ Symbol is USDT pair, continuing...`);

  // Check maximum leverage - only trade if max leverage > 20
  const maxLeverage = getMaxLeverage(symbol);
  if (maxLeverage <= 20) {
    logInfo(`   ⚠️ Skipping trade - maximum leverage (${maxLeverage}x) is <= 20x. Fair trading requires leverage > 20x.`);
    return;
  }

  stats.tradeExecutionsStarted++;
  stats.tradeExecutionsStartedFair++;
  logInfo(`   🔄 Starting order execution for ${symbol}... (execution #${stats.tradeExecutionsStarted})`);
  logInfo(`   📊 Maximum leverage: ${maxLeverage}x (required: > 20x)`);
  await openTradeFromSignal({
    symbol,
    strategy: 'fair',
    isLong,
    entryPrice: currentPrice,
    referencePrice: markPrice,
    initialSpread: diffPercent,
    openType: 1, // Isolated for FAIR strategy (1=isolated, 2=cross)
    marginOverride: Number(available_balance) * (FAIR_FIXED_MARGIN_PERCENT / 100),
    cooldownMs: LAST_CLOSE_DIRECTION_COOLDOWN_MS,
    applySlippageCap: true,
    skipTpLimitPlacement: false
  });
}

// Orderbook updater for MEXC WebSocket
async function orderbookUpdater(symbol) {
  const uri = "wss://contract.mexc.com/edge";
  let backoff = 5000;
  while (true) {
    try {
      const ws = new WebSocket(uri, { headers: { "User-Agent": USER_AGENT } });
      ws.on('open', () => {
        backoff = 5000; // reset backoff on successful open
        const orderbookSub = { method: "sub.depth.full", param: { symbol, limit: ORDERBOOK_DEPTH } };
        ws.send(JSON.stringify(orderbookSub));
        logInfo(`📊 Subscribed to orderbook for ${symbol} (depth=${ORDERBOOK_DEPTH})`);
      });
      ws.on('message', data => {
        try {
          const msg = JSON.parse(data);
          if (msg.channel === "push.depth.full" && msg.data && typeof msg.data === "object") {
            if (msg.symbol !== symbol) return;
            const bids = msg.data.bids || [];
            const asks = msg.data.asks || [];
            if (!orderbooks[symbol]) {
              orderbooks[symbol] = {
                buy_orders: [],
                sell_orders: [],
                best_buy: null,
                best_sell: null,
                depthTs: null,
                _counted: false
              };
            }
            const ob = orderbooks[symbol];
            ob.buy_orders = bids.map(entry => [Number(entry[0]), Number(entry[1])]).sort((a, b) => b[0] - a[0]);
            ob.sell_orders = asks.map(entry => [Number(entry[0]), Number(entry[1])]).sort((a, b) => a[0] - b[0]);
            ob.best_buy = ob.buy_orders.length > 0 ? ob.buy_orders[0][0] : null;
            ob.best_sell = ob.sell_orders.length > 0 ? ob.sell_orders[0][0] : null;
            ob.depthTs = Date.now();
            updateOrderbookReadyState(symbol, Boolean(ob.best_buy && ob.best_sell));
            recordMexcPriceSample(symbol, ob.best_buy, ob.best_sell);

            // Check GMGN positions for closure on orderbook update (если биржа обновилась, а DEX нет)
            // Используем последнюю цену GMGN из кеша для проверки закрытия
            const trade = getActiveTrade(symbol);
            if (trade && trade.strategy === 'gmgn') {
              const tokenKey = gmgnSymbolToTokenKey[symbol];
              const gmgnPrice = tokenKey ? gmgnPrices[tokenKey] : null;
              if (gmgnPrice) {
                monitorGmgnPositionsForClosure(symbol, gmgnPrice).catch(err => {
                  logError(`Error in monitorGmgnPositionsForClosure for ${symbol} on orderbook update: ${err.message}`);
                });
              }
            }

            // Spot-futures strategy removed: no arbitrage hooks here
          }
        } catch (err) {
          logError(`Error processing orderbook message for ${symbol}: ${err.message}`);
        }
      });
      ws.on('error', err => {
        logError(`Orderbook WS error for ${symbol}: ${err.message}`);
        ws.close();
      });
      ws.on('close', () => {
        logWarn(`Orderbook WS closed for ${symbol}`);
        if (orderbooks[symbol]) {
          orderbooks[symbol].best_buy = null;
          orderbooks[symbol].best_sell = null;
          orderbooks[symbol].depthTs = null;
          updateOrderbookReadyState(symbol, false);
        }
      });
      const pingInterval = setInterval(() => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({ method: "ping" }));
        }
      }, 10000);
      await new Promise(resolve => ws.on('close', resolve));
      clearInterval(pingInterval);
      ws.terminate();
    } catch (err) {
      logError(`Orderbook WS error for ${symbol}: ${err.message}`);
    }
    await new Promise(resolve => setTimeout(resolve, backoff));
    backoff = Math.min(backoff * 2, 60000);
  }
}

// MEXC Personal WebSocket for position updates
async function mexcPositionWebSocket() {
  const uri = "wss://contract.mexc.com/edge";
  let backoff = 5000;

  while (true) {
    try {
      const ws = new WebSocket(uri, { headers: { "User-Agent": USER_AGENT } });

      ws.on('open', () => {
        logInfo("✅ Connected to MEXC Personal WebSocket");
        // Login first
        const loginMsg = { method: "login", param: { token: MEXC_KEY } };
        ws.send(JSON.stringify(loginMsg));
        logInfo("📡 Sent login message to MEXC Personal WS");

        // Subscribe to all positions (no symbol filter to get all positions)
        const positionSub = { method: "sub.personal.position", param: {} };
        ws.send(JSON.stringify(positionSub));
        logInfo("📡 Subscribed to personal position channel");
      });

      ws.on('message', data => {
        try {
          const msg = JSON.parse(data.toString());

          // Handle pong messages and login success
          if (msg.channel === "pong" || (msg.code === 200 && msg.msg === "success")) {
            return;
          }

          // Handle position updates
          if (msg.channel === "push.personal.position" && msg.data) {
            logInfo(`   📥 Received position update from WebSocket: ${JSON.stringify(msg.data)}`);
            // Handle both array and single object formats
            const positions = Array.isArray(msg.data) ? msg.data : [msg.data];
            for (const pos of positions) {
              if (pos && pos.symbol) {
                handlePositionUpdate(pos);
              } else {
                logWarn(`   ⚠️ Invalid position data in update: ${JSON.stringify(pos)}`);
              }
            }
          } else if (msg.channel === "push.personal.position") {
            logWarn(`   ⚠️ Position update message missing data: ${JSON.stringify(msg)}`);
          }
        } catch (err) {
          logError(`Error processing MEXC Personal WS message: ${err.message}`);
        }
      });

      ws.on('error', err => {
        logError(`MEXC Personal WebSocket error: ${err.message}`);
        if (ws.readyState !== WebSocket.CLOSED && ws.readyState !== WebSocket.CLOSING) {
          ws.close();
        }
      });

      ws.on('close', () => {
        logWarn("🔌 MEXC Personal WebSocket closed, reconnecting...");
      });

      // Ping every 10 seconds
      const pingInterval = setInterval(() => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({ method: "ping" }));
        }
      }, 10000);

      await new Promise(resolve => ws.on('close', resolve));
      clearInterval(pingInterval);
      ws.terminate();
    } catch (err) {
      logError(`MEXC Personal WebSocket connection error: ${err.message}`);
      await new Promise(resolve => setTimeout(resolve, backoff));
      backoff = Math.min(backoff * 2, 60000);
    }
  }
}

// MEXC WebSocket for ticker updates
async function mexcTickerWebSocket() {
  const uri = "wss://contract.mexc.com/edge";
  let backoff = 5000;

  while (true) {
    try {
      const ws = new WebSocket(uri, { headers: { "User-Agent": USER_AGENT } });

      ws.on('open', () => {
        logInfo("✅ Connected to MEXC WebSocket");
        // Subscribe to all tickers
        const subscribeMsg = { method: "sub.tickers", param: {} };
        ws.send(JSON.stringify(subscribeMsg));
        logInfo("📡 Subscribed to all tickers (sub.tickers)");
      });

      ws.on('message', data => {
        try {
          const msg = JSON.parse(data.toString());

          // Handle pong messages
          if (msg.channel === "pong" || (msg.code === 200 && msg.msg === "success")) {
            return;
          }

          // Handle ticker updates
          if (msg.channel === "push.tickers" && msg.data && Array.isArray(msg.data)) {

            stats.totalMessagesReceived++; // Count batch messages
            stats.totalTickersReceived += msg.data.length; // Count total ticker updates
            stats.lastWebSocketUpdate = Date.now();

            let validTickers = 0;
            let invalidTickers = 0;

            for (const ticker of msg.data) {
              if (!ticker.symbol) {
                invalidTickers++;
                continue;
              }

              const symbol = ticker.symbol;

              // Skip blacklisted symbols
              if (BLACKLISTED_SYMBOLS.has(symbol)) {
                continue;
              }

              // MEXC uses 'fairPrice' for mark price (fair price)
              const markPrice = parseFloat(ticker.fairPrice || ticker.markPrice || ticker.mark_price || ticker.fair_price || 0);
              // Try multiple fields for last price
              const lastPrice = parseFloat(
                ticker.lastPrice ||
                ticker.last_price ||
                ticker.price ||
                ticker.closePrice ||
                ticker.close_price ||
                0
              );

              // Skip if mark price or last price is invalid
              if (isNaN(markPrice) || isNaN(lastPrice) || markPrice <= 0 || lastPrice <= 0) {
                invalidTickers++;
                // Log only first occurrence per symbol to avoid spam
                if (markPrice > 0 && lastPrice === 0 && !zeroLastPriceWarnings[symbol]) {
                  zeroLastPriceWarnings[symbol] = true;
                  // Only log first 3 unique symbols with this issue
                  if (Object.keys(zeroLastPriceWarnings).length <= 3) {
                    logWarn(`⚠️ ${symbol}: fairPrice=${markPrice} but lastPrice=0 (no trading activity - will skip)`);
                  }
                }
                continue;
              }

              validTickers++;

              // Initialize orderbook structure if not exists (for USDT pairs)
              if (!symbolIsUSDT[symbol] && symbol.endsWith('_USDT')) {
                symbolIsUSDT[symbol] = true;
              }
              if (symbolIsUSDT[symbol] && !orderbooks[symbol]) {
                orderbooks[symbol] = {
                  buy_orders: [],
                  sell_orders: [],
                  best_buy: null,
                  best_sell: null,
                  depthTs: null,
                  _counted: false
                };
                // Start orderbook updater for this symbol if not already started
                if (!BLACKLISTED_SYMBOLS.has(symbol) && !orderbookUpdatersStarted.has(symbol)) {
                  orderbookUpdatersStarted.add(symbol);
                  orderbookUpdater(symbol);
                }
              }

              // Update ticker data
              tickerData[symbol] = {
                markPrice,
                lastPrice,
                lastUpdate: Date.now()
              };

              // Process ticker for trading opportunity
              processTicker(symbol, markPrice, lastPrice).catch(err => {
                logError(`Error processing ticker ${symbol}: ${err.message}`);
              });
            }

            // Log batch processing stats occasionally
            if (stats.totalTickersReceived % 1000 === 0) {
              logInfo(`Processed batch: ${validTickers} valid, ${invalidTickers} invalid tickers`);
            }
          }
        } catch (err) {
          logError(`Error processing WebSocket message: ${err.message}`);
        }
      });

      ws.on('error', err => {
        logError(`MEXC WebSocket error: ${err.message}`);
        if (ws.readyState !== WebSocket.CLOSED && ws.readyState !== WebSocket.CLOSING) {
          ws.close();
        }
      });

      ws.on('close', () => {
        logWarn("🔌 MEXC WebSocket closed, reconnecting...");
      });

      // Ping every 10 seconds
      const pingInterval = setInterval(() => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(JSON.stringify({ method: "ping" }));
        }
      }, 10000);

      // Wait for connection to close
      await new Promise(resolve => {
        ws.on('close', () => {
          clearInterval(pingInterval);
          resolve();
        });
      });

      ws.terminate();
    } catch (err) {
      logError(`MEXC WebSocket connection error: ${err.message}`);
    }

    await new Promise(resolve => setTimeout(resolve, backoff));
    backoff = Math.min(backoff * 2, 60000);
  }
}

// Get statistics for last 24 hours
function getStatsForLast24Hours() {
  try {
    loadDailyStats();
    
    const now = Date.now();
    const last24Hours = now - (24 * 60 * 60 * 1000);
    
    const recentTrades = dailyStats.trades.filter(t => {
      const tradeTime = t.timestamp || t.processedAt || 0;
      return tradeTime >= last24Hours;
    });
    
    if (recentTrades.length === 0) {
      return null;
    }
    
    const openTrades = recentTrades.filter(t => t.type === 'open');
    const closedTrades = recentTrades.filter(t => t.type === 'close');
    
    const tickerStats = {};
    let totalPnl = 0;
    
    for (const trade of closedTrades) {
      const ticker = trade.symbol || 'UNKNOWN';
      if (!tickerStats[ticker]) {
        tickerStats[ticker] = { count: 0, pnl: 0 };
      }
      tickerStats[ticker].count++;
      if (trade.pnl !== undefined && Number.isFinite(trade.pnl)) {
        tickerStats[ticker].pnl += trade.pnl;
        totalPnl += trade.pnl;
      }
    }
    
    const totalOpened = openTrades.length;
    const totalClosed = closedTrades.length;
    
    let message = `📊 *СТАТИСТИКА ЗА ПОСЛЕДНИЕ 24 ЧАСА*\n\n`;
    message += `📈 Открыто позиций: ${totalOpened}\n`;
    message += `📉 Закрыто позиций: ${totalClosed}\n`;
    message += `💰 *Общий PnL: ${totalPnl >= 0 ? '+' : ''}$${totalPnl.toFixed(2)}*\n\n`;
    
    if (Object.keys(tickerStats).length > 0) {
      message += `*По тикерам:*\n`;
      const sortedTickers = Object.entries(tickerStats).sort((a, b) => b[1].pnl - a[1].pnl);
      for (const [ticker, stats] of sortedTickers.slice(0, 20)) {
        const pnlSign = stats.pnl >= 0 ? '+' : '';
        message += `• \`${ticker}\`: ${stats.count} сделок, ${pnlSign}$${stats.pnl.toFixed(2)}\n`;
      }
    }
    
    return message;
  } catch (err) {
    logError('Error getting stats for last 24 hours:', err.message);
    return null;
  }
}

// Send daily statistics summary
function sendDailyStats() {
  if (!bot) return;
  try {
    const now = Date.now();
    
    if (dailyStats.lastStatsSentAt && (now - dailyStats.lastStatsSentAt) < STATS_INTERVAL_MS) {
      return;
    }
    
    if (dailyStats.trades.length === 0) {
      dailyStats.lastStatsSentAt = now;
      saveDailyStats();
      return;
    }
    
    const openTrades = dailyStats.trades.filter(t => t.type === 'open');
    const closedTrades = dailyStats.trades.filter(t => t.type === 'close');
    
    const tickerStats = {};
    for (const trade of closedTrades) {
      const ticker = trade.symbol || 'unknown';
      if (!tickerStats[ticker]) {
        tickerStats[ticker] = { count: 0, pnl: 0 };
      }
      tickerStats[ticker].count++;
      tickerStats[ticker].pnl += trade.pnl || 0;
    }
    
    const totalPnl = closedTrades.reduce((sum, t) => sum + (t.pnl || 0), 0);
    const totalOpened = openTrades.length;
    const totalClosed = closedTrades.length;
    
    let message = `📊 *СТАТИСТИКА ЗА 24 ЧАСА*\n\n`;
    message += `📈 Открыто позиций: ${totalOpened}\n`;
    message += `📉 Закрыто позиций: ${totalClosed}\n`;
    message += `💰 *Общий PnL: ${totalPnl >= 0 ? '+' : ''}$${totalPnl.toFixed(2)}*\n\n`;
    
    if (Object.keys(tickerStats).length > 0) {
      message += `*По тикерам:*\n`;
      const sortedTickers = Object.entries(tickerStats).sort((a, b) => b[1].pnl - a[1].pnl);
      for (const [ticker, stats] of sortedTickers.slice(0, 20)) {
        const pnlSign = stats.pnl >= 0 ? '+' : '';
        message += `• \`${ticker}\`: ${stats.count} сделок, ${pnlSign}$${stats.pnl.toFixed(2)}\n`;
      }
    }
    
    bot.sendMessage(ALLOWED_USER_ID, message, { parse_mode: 'Markdown' });
    
    dailyStats = {
      date: new Date().toISOString().split('T')[0],
      trades: [],
      lastStatsSentAt: now
    };
    saveDailyStats();
    
  } catch (err) {
    logError('Error sending daily stats:', err.message);
  }
}

// Check for key change alerts
function checkKeyAlerts() {
  if (!bot) return;
  try {
    if (!fs.existsSync(KEY_ALERT_FILE)) return;
    
    const content = fs.readFileSync(KEY_ALERT_FILE, 'utf8');
    const alerts = JSON.parse(content);
    const now = Date.now();
    
    if (alerts.fair && (now - lastSpreadKeyAlert > KEY_ALERT_COOLDOWN_MS)) {
      lastSpreadKeyAlert = now;
      bot.sendMessage(ALLOWED_USER_ID, `⚠️ *spread.js*: Ваш веб ключ сменился, пожалуйста поменяйте его!`, {
        parse_mode: 'Markdown'
      });
    }
    
    if (alerts.fair) {
      fs.writeFileSync(KEY_ALERT_FILE, JSON.stringify({ spread: false, fair: false, servers: {} }));
    }
  } catch (err) {
    // Ignore errors
  }
}

// Main function
async function main() {
  logInfo("🚀 Starting MEXC Fair Price Trader with API Balance Check");
  logInfo(`Configuration:`);
  logInfo(`   Threshold LONG: ${(FAIR_PRICE_THRESHOLD_LONG * 100).toFixed(2)}% ${ENABLE_LONG ? '✅ ENABLED' : '❌ DISABLED'}`);
  logInfo(`   Threshold SHORT: ${(FAIR_PRICE_THRESHOLD_SHORT * 100).toFixed(2)}% ${ENABLE_SHORT ? '✅ ENABLED' : '❌ DISABLED'}`);
  logInfo(`   TP Limits: TP1=${(TP_LIMIT_1_PCT * 100).toFixed(2)}%, TP2=${(TP_LIMIT_2_PCT * 100).toFixed(2)}%, TP3=${(TP_LIMIT_3_PCT * 100).toFixed(2)}%`);
  logInfo(`   Default Min Margin: ${DEFAULT_MIN_MARGIN_USDT} USDT (will use API value if available)`);
  logInfo(`   Max Leverage: ${MAX_LEVERAGE}x`);
  logInfo(`   Max Open Positions: ${MAX_OPEN_POSITIONS}`);
  logInfo(`   GMGN Spread Trading: ${ENABLE_GMGN_SPREAD_TRADING ? '✅ ENABLED' : '❌ DISABLED'}`);

  // Load blacklists from files
  logInfo("📂 Loading blacklists...");
  // Load blacklist_spread.json for GMGN strategy
  loadSpreadBlacklistFromFile();
  // Load stop-loss banlist
  loadStopLossBlacklistFromFile();
  startSpreadBlacklistReloader();
  watchSpreadBlacklistFile();
  // Load blacklist_fair.json for FAIR strategy
  loadFairBlacklistFromFile();
  startFairBlacklistReloader();
  watchFairBlacklistFile();

  // Get initial balance using API keys
  logInfo("🔑 Checking account balance...");
  await getAccountBalance();

  // Sync server time on startup
  logInfo("⏰ Synchronizing server time...");
  await syncMexcServerTime(true); // Force sync on startup

  // Start periodic server time sync (every 60 seconds)
  setInterval(async () => {
    try {
      await syncMexcServerTime(true); // Force sync periodically
    } catch (err) {
      logWarn(`Failed to sync server time: ${err.message}`);
    }
  }, MEXC_SERVER_TIME_SYNC_INTERVAL_MS);

  // Fetch contract details and balance
  await refreshContractDetails('startup');

  if (!balanceReady) {
    logError("❌ Balance not ready. Cannot proceed.");
    process.exit(1);
  }

  // Start periodic status updates (every 30 seconds)
  setInterval(() => {
    printStatusUpdate();
  }, 30000);

  // Periodic balance refresh every 2 minutes
  setInterval(() => {
    refreshBalance('periodic');
  }, 120000);

  // Hourly balance fetch to detect 401 (web key changed) and notify via key_alert.json
  setInterval(async () => {
    try {
      const result = await getAccountBalance();
      if (result === null && balanceReady) {
        logWarn('Hourly balance check failed (e.g. 401) - key_alert written if 401');
      }
    } catch (err) {
      logError(`Hourly balance check error: ${err.message}`);
    }
  }, 60 * 60 * 1000);

  // Periodic contract details refresh (maxVol updates)
  setInterval(() => {
    refreshContractDetails('periodic').catch(err => logError(`Contract refresh error: ${err.message}`));
  }, 5 * 60 * 1000);

  // Periodic retry of pending TP orders that failed to place
  // Check every 500ms to keep retries timely
  setInterval(() => {
    retryPendingTPOrders().catch(err => logError(`TP retry error: ${err.message}`));
  }, 500); // Check every 500ms

  // Start WebSocket for ticker updates
  mexcTickerWebSocket();

  // Start WebSocket for position updates
  mexcPositionWebSocket();

  // Start GMGN spread strategy (from mexc_tp.js) in parallel (non-blocking)
  if (ENABLE_GMGN_SPREAD_TRADING) {
    (async () => {
      try {
        await setupGmgnSubscriptions();
        // Fire-and-forget: this paces connections and starts per-token GMGN websockets
        startGmgnWebsockets().catch(err => logWarn(`[GMGN] startGmgnWebsockets exited: ${err.message || err}`));

        // Periodic maintenance tasks (parity with mexc_tp.js)
        refreshDailyVolumesPeriodically().catch(err => logWarn(`[GMGN][Volume] Periodic task exited: ${err.message || err}`));
        refreshDepositWithdrawStatusPeriodically().catch(err => logWarn(`[GMGN][D/W] Periodic task exited: ${err.message || err}`));
      } catch (err) {
        logError(`[GMGN] Failed to initialize GMGN strategy: ${err.message || err}`);
      }
    })();
  }

  // Spot-futures strategy removed from runtime startup.

  // Periodic slippage-based sizing scan (uses live orderbooks)
  if (OB_SCAN_INTERVAL_MS > 0) {
    setInterval(() => {
      scanOrderbooksForSlippage().catch(err => logError(`Slippage scan error: ${err.message}`));
    }, OB_SCAN_INTERVAL_MS);
  }

  // Start orderbook updaters for all USDT symbols
  // Wait a bit for contract details to load, then start orderbook updaters
  setTimeout(() => {
    const usdtSymbols = Object.keys(contract_details).filter(symbol => {
      if (!symbolIsUSDT[symbol]) {
        symbolIsUSDT[symbol] = symbol.endsWith('_USDT');
      }
      return symbolIsUSDT[symbol] && !BLACKLISTED_SYMBOLS.has(symbol);
    });
    logInfo(`📊 Starting orderbook updaters for up to ${Math.min(usdtSymbols.length, MAX_ORDERBOOK_SOCKETS)} USDT symbols (cap=${MAX_ORDERBOOK_SOCKETS})...`);
    let started = 0;
    for (const symbol of usdtSymbols) {
      if (started >= MAX_ORDERBOOK_SOCKETS) {
        logWarn(`🚦 Reached MAX_ORDERBOOK_SOCKETS=${MAX_ORDERBOOK_SOCKETS}, skipping remaining symbols.`);
        break;
      }
      // Initialize orderbook structure
      if (!orderbooks[symbol]) {
        orderbooks[symbol] = {
          buy_orders: [],
          sell_orders: [],
          best_buy: null,
          best_sell: null,
          depthTs: null,
          _counted: false
        };
      }
      // Start orderbook updater (non-blocking) if not already started
      if (!orderbookUpdatersStarted.has(symbol)) {
        orderbookUpdatersStarted.add(symbol);
        orderbookUpdater(symbol);
        started++;
      }
    }
    // Prime slippage scan once after initial OB updaters start
    scanOrderbooksForSlippage().catch(err => logError(`Slippage scan error: ${err.message}`));
  }, 2000); // Wait 2 seconds for contract details to load
  
  // Initialize Telegram bot commands if bot is available
  if (bot) {
    initializeTelegramBot();
  }
}

// Initialize Telegram bot commands
function initializeTelegramBot() {
  if (!bot) return;
  
  // Create main menu keyboard
  function getMainMenuKeyboard() {
    return {
      keyboard: [
        [
          { text: '💰 Баланс' },
          { text: '🪙 Токен' }
        ],
        [
          { text: '🚫 Бан/Разбан' },
          { text: '⏹️ Остановить' }
        ],
        [
          { text: '🔄 Перезапустить' },
          { text: '🔑 Ключ' }
        ],
        [
          { text: '📊 Статистика' }
        ],
        [
          { text: '🔍 Статус' }
      ]
    ],
    resize_keyboard: true,
    one_time_keyboard: false
    };
  }
  
  // Command: /start or /menu
  bot.onText(/\/(start|menu)/, async (msg) => {
    if (!isAuthorized(msg)) return;
    menuHistory.delete(msg.chat.id);
    const message = `🤖 *Главное меню*\n\nВыберите действие:`;
    bot.sendMessage(msg.chat.id, message, {
      parse_mode: 'Markdown',
      reply_markup: getMainMenuKeyboard()
    });
  });
  
  // Command: /help
  bot.onText(/\/help/, async (msg) => {
    if (!isAuthorized(msg)) return;
    const message = `🤖 *Главное меню*\n\nВыберите действие:`;
    bot.sendMessage(msg.chat.id, message, {
      parse_mode: 'Markdown',
      reply_markup: getMainMenuKeyboard()
    });
  });
  
  // Command: /balance
  bot.onText(/\/balance$/, async (msg) => {
    if (!isAuthorized(msg)) return;
    try {
      const balances = { futures: available_balance, spot: null };
      let message = '💰 *БАЛАНСЫ АККАУНТОВ*\n';
      message += '━━━━━━━━━━━━━━━━━━\n\n';
      
      const futuresBalance = balances.futures !== null && Number.isFinite(balances.futures) ? balances.futures : null;
      if (futuresBalance !== null) {
        message += `📈 *Futures:*\n`;
        message += `   💵 $${futuresBalance.toFixed(2)} USDT\n`;
      } else {
        message += `📈 *Futures:*\n`;
        message += `   ⚠️ Недоступен\n`;
      }
      
      message += '\n';
      message += `💵 *Spot:*\n`;
      message += `   ⚠️ Недоступен\n`;
      
      if (futuresBalance !== null) {
        message += '\n━━━━━━━━━━━━━━━━━━\n';
        message += `💸 *ВСЕГО:* $${futuresBalance.toFixed(2)} USDT`;
      }
      
      bot.sendMessage(msg.chat.id, message, { parse_mode: 'Markdown' });
    } catch (err) {
      bot.sendMessage(msg.chat.id, `❌ Ошибка при получении балансов: ${err.message}`);
    }
  });
  
  // Command: /stats
  bot.onText(/\/stats$/, async (msg) => {
    if (!isAuthorized(msg)) return;
    const stats = getStatsForLast24Hours();
    if (stats) {
      bot.sendMessage(msg.chat.id, stats, { parse_mode: 'Markdown' });
    } else {
      bot.sendMessage(msg.chat.id, '📊 Нет данных за последние 24 часа');
    }
  });
  
  // Command: /ban <ticker>
  bot.onText(/\/ban\s+(.+)/, async (msg, match) => {
    if (!isAuthorized(msg)) return;
    const ticker = match[1].trim().toUpperCase();
    bot.sendMessage(msg.chat.id, `⏳ Баню токен ${ticker}...`);
    const result = addToBlacklist(BLACKLIST_FAIR_FILE, ticker);
    if (result.success) {
      if (result.alreadyExists) {
        bot.sendMessage(msg.chat.id, `⚠️ ${ticker} уже в бан-листе`);
      } else {
        BLACKLISTED_SYMBOLS.add(ticker.includes('_USDT') ? ticker : `${ticker}_USDT`);
        bot.sendMessage(msg.chat.id, `✅ ${ticker} добавлен в blacklist_fair.json`);
      }
    } else {
      bot.sendMessage(msg.chat.id, `❌ Ошибка: ${result.error}`);
    }
  });
  
  // Command: /unban <ticker>
  bot.onText(/\/unban\s+(.+)/, async (msg, match) => {
    if (!isAuthorized(msg)) return;
    const ticker = match[1].trim().toUpperCase();
    const result = removeFromBlacklist(BLACKLIST_FAIR_FILE, ticker);
    if (result.success) {
      if (result.notFound) {
        bot.sendMessage(msg.chat.id, `⚠️ ${ticker} не найден в бан-листе`);
      } else {
        const normalized = ticker.includes('_USDT') ? ticker : `${ticker}_USDT`;
        BLACKLISTED_SYMBOLS.delete(normalized);
        bot.sendMessage(msg.chat.id, `✅ ${ticker} удалён из blacklist_fair.json`);
      }
    } else {
      bot.sendMessage(msg.chat.id, `❌ Ошибка: ${result.error}`);
    }
  });
  
  // Handle reply keyboard buttons
  bot.on('message', async (msg) => {
    if (!isAuthorized(msg)) return;
    if (msg.text && msg.text.startsWith('/')) return;
    
    const text = msg.text?.trim() || '';
    
    if (text === '💰 Баланс') {
      try {
        let message = '💰 *Баланс аккаунта*\n\n';
        if (available_balance !== null && Number.isFinite(available_balance)) {
          message += `💵 *${available_balance.toFixed(2)} USDT*`;
        } else {
          message += '⚠️ Баланс недоступен';
        }
        bot.sendMessage(msg.chat.id, message, { parse_mode: 'Markdown', reply_markup: getMainMenuKeyboard() });
      } catch (err) {
        bot.sendMessage(msg.chat.id, `❌ Ошибка: ${err.message}`, { reply_markup: getMainMenuKeyboard() });
      }
      return;
    }
    
    if (text === '📊 Статистика') {
      const stats = getStatsForLast24Hours();
      if (stats) {
        bot.sendMessage(msg.chat.id, stats, { parse_mode: 'Markdown', reply_markup: getMainMenuKeyboard() });
      } else {
        bot.sendMessage(msg.chat.id, '📊 Нет данных за последние 24 часа', { reply_markup: getMainMenuKeyboard() });
      }
      return;
    }
    
    if (text === '🔑 Ключ') {
      userStates.set(msg.chat.id, {
        step: 'change_web_key',
        data: {}
      });
      bot.sendMessage(msg.chat.id, '🔑 *Смена WEB ключа*\n\nВведите новый WEB ключ:\n\nФормат: WEB...', {
        parse_mode: 'Markdown',
        reply_markup: { remove_keyboard: true }
      });
      return;
    }
    
    if (text === '🪙 Токен') {
      if (!menuHistory.has(msg.chat.id)) {
        menuHistory.set(msg.chat.id, []);
      }
      menuHistory.get(msg.chat.id).push('main');
      
      const tokenKeyboard = {
        keyboard: [
          [
            { text: '➕ Добавить токен' },
            { text: '✏️ Изменить токен' }
          ],
          [
            { text: '🗑️ Удалить токен' }
          ],
          [
            { text: '⬅️ Назад' }
          ]
        ],
        resize_keyboard: true,
        one_time_keyboard: false
      };
      bot.sendMessage(msg.chat.id, '🪙 *Управление токенами*\n\nВыберите действие:', {
        parse_mode: 'Markdown',
        reply_markup: tokenKeyboard
      });
      return;
    }
    
    if (text === '🚫 Бан/Разбан') {
      if (!menuHistory.has(msg.chat.id)) {
        menuHistory.set(msg.chat.id, []);
      }
      menuHistory.get(msg.chat.id).push('main');
      
      const banKeyboard = {
        keyboard: [
          [
            { text: '🚫 Бан' },
            { text: '✅ Разбан' }
          ],
          [
            { text: '⬅️ Назад' }
          ]
        ],
        resize_keyboard: true,
        one_time_keyboard: false
      };
      bot.sendMessage(msg.chat.id, '🚫 *Бан/Разбан токенов*\n\nВыберите действие:', {
        parse_mode: 'Markdown',
        reply_markup: banKeyboard
      });
      return;
    }
    
    if (text === '⏹️ Остановить') {
      bot.sendMessage(msg.chat.id, '⏳ Останавливаю spread.js...');
      const stopped = await stopPm2Process('spread');
      if (stopped) {
        bot.sendMessage(msg.chat.id, '✅ spread.js остановлен', { reply_markup: getMainMenuKeyboard() });
      } else {
        bot.sendMessage(msg.chat.id, '⚠️ Не удалось остановить процесс spread (возможно уже остановлен или не запущен через PM2)', { reply_markup: getMainMenuKeyboard() });
      }
      return;
    }
    
    if (text === '🔄 Перезапустить') {
      bot.sendMessage(msg.chat.id, '⏳ Перезапускаю spread.js...');
      const restarted = await restartPm2Process('spread');
      if (restarted) {
        bot.sendMessage(msg.chat.id, '✅ spread.js перезапущен', { reply_markup: getMainMenuKeyboard() });
      } else {
        bot.sendMessage(msg.chat.id, '❌ Не удалось перезапустить spread (возможно не запущен через PM2)', { reply_markup: getMainMenuKeyboard() });
      }
      return;
    }
    
    if (text === '🔍 Статус') {
      userStates.set(msg.chat.id, {
        step: 'check_deposit_withdraw_status',
        data: {}
      });
      bot.sendMessage(msg.chat.id, '🔍 *Проверка статуса депозита/вывода*\n\nВведите тикер (например: TRUMP):', {
        parse_mode: 'Markdown',
        reply_markup: { remove_keyboard: true }
      });
      return;
    }
    
    if (text === '⬅️ Назад') {
      const history = menuHistory.get(msg.chat.id);
      if (!history || history.length === 0) {
        bot.sendMessage(msg.chat.id, '🤖 *Главное меню*\n\nВыберите действие:', {
          parse_mode: 'Markdown',
          reply_markup: getMainMenuKeyboard()
        });
        return;
      }
      const previousMenu = history.pop();
      if (previousMenu === 'main') {
        bot.sendMessage(msg.chat.id, '🤖 *Главное меню*\n\nВыберите действие:', {
          parse_mode: 'Markdown',
          reply_markup: getMainMenuKeyboard()
        });
      }
      return;
    }
    
    if (text === '🚫 Бан') {
      if (!menuHistory.has(msg.chat.id)) {
        menuHistory.set(msg.chat.id, []);
      }
      menuHistory.get(msg.chat.id).push('ban');
      
      userStates.set(msg.chat.id, {
        step: 'ban_ticker',
        data: {}
      });
      bot.sendMessage(msg.chat.id, '🚫 *Бан токена*\n\nВведите название тикера (например: TRUMP):', {
        parse_mode: 'Markdown',
        reply_markup: { remove_keyboard: true }
      });
      return;
    }
    
    if (text === '✅ Разбан') {
      if (!menuHistory.has(msg.chat.id)) {
        menuHistory.set(msg.chat.id, []);
      }
      menuHistory.get(msg.chat.id).push('ban');
      
      userStates.set(msg.chat.id, {
        step: 'unban_ticker',
        data: {}
      });
      bot.sendMessage(msg.chat.id, '✅ *Разбан токена*\n\nВведите название тикера (например: TRUMP):', {
        parse_mode: 'Markdown',
        reply_markup: { remove_keyboard: true }
      });
      return;
    }
    
    // Handle conversation states
    const state = userStates.get(msg.chat.id);
    if (!state) return;
    
    if (state.step === 'change_web_key') {
      if (!text.startsWith('WEB') || text.length < 50) {
        bot.sendMessage(msg.chat.id, '❌ Неверный формат ключа. Ключ должен начинаться с WEB и быть длинным.\nВведите еще раз:');
        return;
      }
      const webKeyResult = updateApiKeysFile(text);
      if (webKeyResult.success) {
        bot.sendMessage(msg.chat.id, `✅ WEB ключ обновлен в api_keys.js!`, { reply_markup: getMainMenuKeyboard() });
      } else {
        bot.sendMessage(msg.chat.id, `❌ Ошибка: ${webKeyResult.error}`, { reply_markup: getMainMenuKeyboard() });
      }
      userStates.delete(msg.chat.id);
      return;
    }
    
    if (state.step === 'ban_ticker') {
      const ticker = text.trim().toUpperCase();
      bot.sendMessage(msg.chat.id, `⏳ Баню токен ${ticker}...`);
      const result = addToBlacklist(BLACKLIST_FAIR_FILE, ticker);
      if (result.success) {
        if (result.alreadyExists) {
          bot.sendMessage(msg.chat.id, `⚠️ ${ticker} уже в бан-листе`, { reply_markup: getMainMenuKeyboard() });
        } else {
          BLACKLISTED_SYMBOLS.add(ticker.includes('_USDT') ? ticker : `${ticker}_USDT`);
          bot.sendMessage(msg.chat.id, `✅ ${ticker} добавлен в blacklist_fair.json`, { reply_markup: getMainMenuKeyboard() });
        }
      } else {
        bot.sendMessage(msg.chat.id, `❌ Ошибка: ${result.error}`, { reply_markup: getMainMenuKeyboard() });
      }
      userStates.delete(msg.chat.id);
      return;
    }
    
    if (state.step === 'unban_ticker') {
      const ticker = text.trim().toUpperCase();
      const result = removeFromBlacklist(BLACKLIST_FAIR_FILE, ticker);
      if (result.success) {
        if (result.notFound) {
          bot.sendMessage(msg.chat.id, `⚠️ ${ticker} не найден в бан-листе`, { reply_markup: getMainMenuKeyboard() });
        } else {
          const normalized = ticker.includes('_USDT') ? ticker : `${ticker}_USDT`;
          BLACKLISTED_SYMBOLS.delete(normalized);
          bot.sendMessage(msg.chat.id, `✅ ${ticker} удалён из blacklist_fair.json`, { reply_markup: getMainMenuKeyboard() });
        }
      } else {
        bot.sendMessage(msg.chat.id, `❌ Ошибка: ${result.error}`, { reply_markup: getMainMenuKeyboard() });
      }
      userStates.delete(msg.chat.id);
      return;
    }
    
    if (state.step === 'check_deposit_withdraw_status') {
      const ticker = text.trim().toUpperCase();
      const mexcName = ticker.endsWith('_USDT') ? ticker : `${ticker}_USDT`;
      bot.sendMessage(msg.chat.id, `🔍 Проверяю статус для ${mexcName}...`, { reply_markup: getMainMenuKeyboard() });
      userStates.delete(msg.chat.id);
      return;
    }
  });
  
  // Handle errors
  bot.on('polling_error', (error) => {
    logError('Polling error:', error.code, error.message);
  });
  
  bot.on('error', (error) => {
    logError('Bot error:', error);
  });
  
  // Check for trade notifications every 5 seconds
  setInterval(checkTradeNotifications, 5000);
  checkTradeNotifications(); // Initial check
  
  // Check for daily stats every hour
  loadDailyStats();
  setInterval(sendDailyStats, 60 * 60 * 1000);
  sendDailyStats(); // Initial check
  
  // Check for key alerts every 30 seconds
  setInterval(checkKeyAlerts, 30000);
  checkKeyAlerts(); // Initial check
  
  logInfo('✅ Telegram bot commands initialized');
}

main().catch(err => {
  logError(`Fatal error: ${err.message}`);
  console.error(err);
  process.exit(1);
});
