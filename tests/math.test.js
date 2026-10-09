const test = require('node:test');
const assert = require('node:assert/strict');
const m = require('../src/math');
const book = () => ({best_buy: 99, best_sell: 100, buy_orders: [[99, 2], [98, 2]], sell_orders: [[100, 2], [101, 2]]});
test('zero slippage permits only best-level liquidity', () => {
  const r = m.slippageCapacity(book(), 0);
  assert.equal(r.longNotional, 200);
  assert.equal(r.shortNotional, 198);
  assert.equal(r.worst, 198);
});
test('partial-level sizing respects VWAP bound', () => {
  const r = m.slippageCapacity(book(), 25);
  // 2 units at 100, then 2/3 of a unit at 101 yields VWAP 100.25.
  assert.ok(Math.abs(r.longNotional - (200 + 101 * 2/3)) < 1e-9);
});
test('contract size scales notional', () => {
  assert.equal(m.slippageCapacity(book(), 0, 0.1).longNotional, 20);
});
test('depth VWAP includes all requested levels', () => {
  const r = m.computeDepthSlippageAtLimit(book(), 2);
  assert.equal(r.longNotional, 402);
  assert.equal(r.shortNotional, 394);
  assert.equal(r.slipAsk, 0.005);
});
test('malformed, crossed or unsorted books fail closed', () => {
  assert.throws(() => m.slippageCapacity({...book(), best_buy: 101}, 50));
  assert.throws(() => m.slippageCapacity({...book(), sell_orders: [[101, 1], [100, 1]]}, 50));
  assert.throws(() => m.slippageCapacity({...book(), buy_orders: [[99, -1]]}, 50));
  assert.throws(() => m.slippageCapacity(book(), NaN));
  assert.throws(() => m.slippageCapacity(book(), 50, -1));
});
