const m = require('./math');
const book = {best_buy: 99, best_sell: 100, buy_orders: [[99, 2], [98, 2]], sell_orders: [[100, 2], [101, 2]]};
console.log(JSON.stringify({fictional: true, capacity: m.slippageCapacity(book, 50), depth: m.computeDepthSlippageAtLimit(book, 2)}, null, 2));
