# Remaining work

1. **IEEE 754 binary64 with normal/subnormal/special-value handling.** `quantize_unit` is `1/2` error (k=0 fixed-precision). Build `(sign, exponent, mantissa)` triple with 11-bit exponent and 52-bit mantissa, round-to-nearest-even, prove `|q(x) − x| ≤ 2^{−53}|x|` for normal-range x, handle subnormals with absolute error `2^{−1074}`, model `+∞ / −∞ / NaN` as an option type with propagation rules.

2. **Hungarian algorithm itself.** Part XVI provides the matching infrastructure (cost matrix, weight, injectivity, max-weight-matching-exists). The polynomial-time `O(n³)` Hungarian constructor with potentials, alternating trees, and augmenting paths is the missing implementation; the existence theorem is its abstract correctness target.
