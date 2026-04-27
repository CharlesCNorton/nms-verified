# Remaining work

1. **Local Lipschitz via IBP.** `Π mat_inf_norm M_i` overestimates by 3–6 orders of magnitude on real networks; the bridge's `m − 2·L·eps` slack goes negative for realistic `m`. Add `Section IntervalLipschitz`: `interval_lipschitz M lo hi L`, prove composition under input boxes, replace `multilayer_lipschitz` instantiations.

2. **Architectural margin derivation.** `lipschitz_bridge_substantive`'s margin hypothesis is undischargeable in practice. `derived_base_score_invariant` and `detr_matching_pairwise_disjoint` already sketch the pattern. Pick one architecture (FCOS or DETR), derive "training equilibrium ⟹ margin ≥ m" as a theorem, not a hypothesis.

3. **Real-architecture worked example.** Replace `c30_D` (2 detections, hand-tuned). Concrete weights, IBP-derived L, 20–50 detection list, `Separated_check` returning `true` by `vm_compute`.

4. **Quantization slack through full network.** `real_lipschitz_to_nat` absorbs one bit at the score head only. Per-layer `vec_quantize` with slack accumulation; prove `multilayer_lipschitz` survives end-to-end.

5. **Replace tautological training framing.** Part VI's `trained_list := nms_sorted` defines training as NMS-output-storage. Replace with actual SGD-on-`L_separated_sq` convergence to a `Separated`-locus minimizer using `SGDDescentVec` + item 7.

6. **Sample complexity composition formula.** `sample_complexity M Var ε δ`: closed-form sufficient sample size from Chebyshev + Bonferroni. Compose existing fragments into a single named theorem.

7. **Convex `SGDDescentVec` global convergence.** Current `sgd_telescoping` proves stationary-point convergence: `min_t |∇f(θ_t)|² ≤ 2(f₀ − f_lower)/(ηT)`. Add `Hypothesis convex` (or Polyak-Łojasiewicz), prove `f(θ_T) − f* ≤ O(1/T)`. Required by item 5.

8. **`L_separated_sq` full zero-locus iff `Separated`.** Per-pair `pair_violation_sq d d' = 0 ↔ pair_violation d d' = 0` is done. Lift to the sum: `L_separated_sq m D = 0 ↔ L_separated m D = 0 ↔ Separated iou tau theta floor(m) D` via `fold_right_Rplus_zero_iff`.

9. **Multi-class `L_separated` with cross-class penalty.** Current `L_separated` is single-class. Extend to `mc_det`: for each high-IoU pair across multi-output detections, sum the violation penalty over all classes. Prove zero-locus equivalence with `mc_one_peak ∧ mc_no_tie_clash`.

10. **Hungarian-optimal weighted bipartite matching.** Greedy gets `min(|boxes|, |gts|)` matches. Build `O(n³)` Hungarian: cost matrix `Box → GT → R`, augmenting paths via alternating trees, slack variables, prove output maximizes `Σ weight(b, gt(b))` while preserving injectivity.

11. **IEEE 754 binary64 with normal/subnormal/special-value handling.** `quantize_unit` is `1/2` error (k=0 fixed-precision). Build `(sign, exponent, mantissa)` triple with 11-bit exponent and 52-bit mantissa, round-to-nearest-even, prove `|q(x) − x| ≤ 2^{−53}|x|` for normal-range x, handle subnormals with absolute error `2^{−1074}`, model `+∞ / −∞ / NaN` as an option type with propagation rules.
