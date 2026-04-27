# Remaining work

1. **Replace tautological training framing.** Part VI's `trained_list := nms_sorted` defines training as NMS-output-storage. Replace with actual SGD-on-`L_separated_sq` convergence to a `Separated`-locus minimizer using `SGDDescentVec` + item 3.

2. **Sample complexity composition formula.** `sample_complexity M Var ε δ`: closed-form sufficient sample size from Chebyshev + Bonferroni. Compose existing fragments into a single named theorem.

3. **Convex `SGDDescentVec` global convergence.** Current `sgd_telescoping` proves stationary-point convergence: `min_t |∇f(θ_t)|² ≤ 2(f₀ − f_lower)/(ηT)`. Add `Hypothesis convex` (or Polyak-Łojasiewicz), prove `f(θ_T) − f* ≤ O(1/T)`. Required by item 1.

4. **`L_separated_sq` full zero-locus iff `Separated`.** Per-pair `pair_violation_sq d d' = 0 ↔ pair_violation d d' = 0` is done. Lift to the sum: `L_separated_sq m D = 0 ↔ L_separated m D = 0 ↔ Separated iou tau theta floor(m) D` via `fold_right_Rplus_zero_iff`.

5. **Multi-class `L_separated` with cross-class penalty.** Current `L_separated` is single-class. Extend to `mc_det`: for each high-IoU pair across multi-output detections, sum the violation penalty over all classes. Prove zero-locus equivalence with `mc_one_peak ∧ mc_no_tie_clash`.

6. **Hungarian-optimal weighted bipartite matching.** Greedy gets `min(|boxes|, |gts|)` matches. Build `O(n³)` Hungarian: cost matrix `Box → GT → R`, augmenting paths via alternating trees, slack variables, prove output maximizes `Σ weight(b, gt(b))` while preserving injectivity.

7. **IEEE 754 binary64 with normal/subnormal/special-value handling.** `quantize_unit` is `1/2` error (k=0 fixed-precision). Build `(sign, exponent, mantissa)` triple with 11-bit exponent and 52-bit mantissa, round-to-nearest-even, prove `|q(x) − x| ≤ 2^{−53}|x|` for normal-range x, handle subnormals with absolute error `2^{−1074}`, model `+∞ / −∞ / NaN` as an option type with propagation rules.
