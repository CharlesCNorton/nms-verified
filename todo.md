# Remaining work

1. **Hungarian-optimal weighted bipartite matching.** Round 3 item 4 delivered count-maximum (greedy gets `min(|boxes|, |gts|)` matches). Build the actual `O(n³)` Hungarian: cost matrix as `Box → GT → R`, augmenting paths via alternating trees, slack variables, prove the algorithm's output maximizes the total weight `Σ weight(b, gt(b))` while preserving injectivity. Replaces "count-greedy is optimal for unit weights" with "Hungarian is optimal for arbitrary cost matrices."

2. **IEEE 754 binary64 with normal/subnormal/special-value handling.** Round 3 item 5 delivered `quantize_unit` with `1/2` error (k=0 fixed-precision). Build the actual binary64 representation: `(sign, exponent, mantissa)` triple with 11-bit exponent and 52-bit mantissa, round-to-nearest-even, prove `|q(x) − x| ≤ 2^{−53}|x|` for normal-range x, handle subnormals with absolute error `2^{−1074}`, model `+∞ / −∞ / NaN` as an option type with propagation rules.

3. **`L_separated_sq` full zero-locus iff `Separated`.** Round 3 item 6 proved per-pair `pair_violation_sq d d' = 0 ↔ pair_violation d d' = 0`. Lift to the sum: `L_separated_sq m D = 0 ↔ L_separated m D = 0 ↔ Separated iou tau theta floor(m) D` (combining with the existing `L_separated_zero_iff_separated_general`). The squared loss has the same zero-locus as the L1 loss.

4. **Multi-class `L_separated` with cross-class penalty.** The current `L_separated` is single-class. Extend to `mc_det` from round 1 item 4: for each high-IoU pair across multi-output detections, sum the violation penalty over all classes. Prove zero-locus equivalence with `mc_one_peak ∧ mc_no_tie_clash`. Connects the multi-output infrastructure to the loss-function infrastructure.

5. **Convex `SGDDescentVec` global-convergence theorem.** Current `sgd_telescoping` proves stationary-point convergence: `min_t |∇f(θ_t)|² ≤ 2(f₀ − f_lower)/(ηT)`. For convex `f`, this implies `f(θ_T) − f* ≤ O(1/T)` (PL inequality). Add a `Hypothesis convex` assumption (or Polyak-Łojasiewicz condition), prove `f(θ_T) − f* → 0` at the standard rate. Promotes "stationary point" to "global minimum."

6. **Sample complexity composition formula.** Compose Chebyshev + Bonferroni into an explicit `sample_complexity` theorem: for finite hypothesis class of size `M`, sample size `n ≥ M·Var / (δ·ε²)` suffices to ensure no hypothesis's empirical violation rate deviates from population by more than `ε` with probability `< δ`. Closed-form sample complexity, parameterised by `M, Var, ε, δ`.
