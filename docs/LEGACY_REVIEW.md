# Legacy review

Source: `spread.js`. The `legacy/` file retains the original strategy logic for inspection with an unconditional early execution guard. This copy intentionally has no supported live invocation.

Original execution flow: Ticker/depth streams → freshness and liquidity filters → sizing and strategy state → signed spot/web-session futures requests → position streams, persistence and Telegram controls.

Changes made to the copy: removed automatic dependency installation; replaced file-based credential loading with environment references; blocked legacy execution before any imports or side effects. Project-specific calculation corrections are in `src/math.js` and do not silently alter the original trading algorithms.

Known concerns:

- The legacy program is a large monolith with duplicated startSpreadBlacklistReloader declarations and shared mutable state.
- Offline math uses floating-point values and assumes sorted valid levels; wrappers validate the public entry point.
- Legacy max leverage and large balance allocations are not validated risk controls.
- Retries, partial fills, order idempotency, funding, fees and crash recovery still require a simulated exchange.
- Local support files and adapter dependencies are missing from the original workspace.

Historical adapter dependencies are not installed by the offline package. Configuration, token maps, blacklists, log/state files and PM2 processes referenced by legacy code are not supplied as real data. Relocating this source changes historical file locations; those paths must be redesigned before a future integration. Neither endpoint compatibility nor live account behavior was verified.
