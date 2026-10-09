'use strict';
// Reviewed order-book VWAP and partial-level sizing from spread.js.
const OB_SCAN_DEPTH_LEVELS = 5;
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

function validateBook(ob, contractSize = 1) {
  if (!ob || !Number.isFinite(contractSize) || contractSize <= 0 || !Number.isFinite(ob.best_buy) || !Number.isFinite(ob.best_sell) || ob.best_buy <= 0 || ob.best_sell <= 0 || ob.best_buy > ob.best_sell) throw new RangeError('Invalid order book');
  for (const [field, ascending] of [['sell_orders', true], ['buy_orders', false]]) {
    if (!Array.isArray(ob[field]) || !ob[field].length) throw new RangeError('Missing levels');
    let previous;
    for (const level of ob[field]) {
      if (!Array.isArray(level) || level.length < 2) throw new RangeError('Invalid level');
      const [price, quantity] = level;
      if (!Number.isFinite(price) || !Number.isFinite(quantity) || price <= 0 || quantity <= 0 || (previous !== undefined && (ascending ? price < previous : price > previous))) throw new RangeError('Invalid or unsorted levels');
      previous = price;
    }
  }
  if (ob.buy_orders[0][0] !== ob.best_buy || ob.sell_orders[0][0] !== ob.best_sell) throw new RangeError('Best quote must match first level');
}
function slippageCapacity(ob, bps, contractSize = 1) {
  validateBook(ob, contractSize);
  if (!Number.isFinite(bps) || bps < 0 || bps >= 10000) throw new RangeError('Invalid basis points');
  return computeMaxNotionalBySlippage(ob, bps, contractSize);
}
module.exports = { calcMaxNotionalForSide, computeDepthSlippageAtLimit, slippageCapacity };
