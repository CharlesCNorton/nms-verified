# Remaining work

1. **IEEE 754 binary64 relative-error / subnormal / special-value extensions.** Part XVII delivers the `b64_repr` record (sign, 11-bit exponent, 52-bit mantissa) and `fp_quantize` / `b64_quantize` with absolute-error bound `q/2`. The full IEEE 754 standard requires: (a) round-to-nearest-even tie-breaking; (b) relative-error bound `|q(x) - x| <= 2^{-53} * |x|` on the normal range, derived via per-x ULP; (c) subnormal range with absolute-error `2^{-1074}` near zero; (d) special-value option type with propagation rules for `+inf / -inf / NaN`.

2. **Hungarian algorithm itself.** Part XVI provides the matching infrastructure (cost matrix, weight, injectivity, max-weight-matching-exists). The polynomial-time `O(n³)` Hungarian constructor with potentials, alternating trees, and augmenting paths is the missing implementation; the existence theorem is its abstract correctness target.
