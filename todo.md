# Remaining work

1. **Hungarian-optimal weighted bipartite matching.** Greedy gets `min(|boxes|, |gts|)` matches. Build `O(n³)` Hungarian: cost matrix `Box → GT → R`, augmenting paths via alternating trees, slack variables, prove output maximizes `Σ weight(b, gt(b))` while preserving injectivity.

2. **IEEE 754 binary64 with normal/subnormal/special-value handling.** `quantize_unit` is `1/2` error (k=0 fixed-precision). Build `(sign, exponent, mantissa)` triple with 11-bit exponent and 52-bit mantissa, round-to-nearest-even, prove `|q(x) − x| ≤ 2^{−53}|x|` for normal-range x, handle subnormals with absolute error `2^{−1074}`, model `+∞ / −∞ / NaN` as an option type with propagation rules.
