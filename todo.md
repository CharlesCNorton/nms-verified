# Remaining work

The pipeline now ships:

  - Optimal weighted bipartite matching with full parametric correctness:
    - Part XIX `brute_match` (constructive O(n!) optimum via permutation enumeration).
    - Part XXII `dp_max_match` (canonical Hungarian-style DP recurrence with parametric equivalence to `brute_match`).
    - Part XXIII LP-duality optimality theorem `hungarian_optimal_via_duality` (perfect matching with dual-feasible / complementary-slack potentials is optimal).
    - Part XXIV `hungarian_witness_optimal` and `hungarian_witness_unique_value` — practical API: any algorithm producing (M, u, v) satisfying `is_hungarian_witness` is provably optimal.

  - Concentration inequalities (Parts VI / XII / XXV):
    - `markov_finite_uniform`, `chebyshev_finite_uniform`, `bonferroni_two`, `bonferroni_list`, `sample_complexity_chebyshev_bonferroni`, `chernoff_markov_bound`.
    - Part XXV `hoeffding_chernoff_chain` and `hoeffding_optimized_lambda` — the Hoeffding tail bound `exp(-2t²/(b-a)²)` follows from the sub-Gaussian MGF assumption via Chernoff + lambda-optimization.

  - Full IEEE 754 binary64 semantics (Parts XVII / XVIII / XXI):
    absolute-error, relative-error scaling, round-to-nearest-even with even-tie property, subnormal range at `2⁻¹⁰⁷⁵` absolute error, full special-value algebra with NaN / inf propagation.

Two analytic completions remain as engineering follow-ups, both genuinely beyond Stdlib's current infrastructure:

1. **Strict polynomial-time O(n³) Hungarian implementation.** Correctness reduces (via Part XXIV) to producing (M, u, v) satisfying `is_hungarian_witness` at termination. The classical algorithm — initialize potentials, find augmenting paths in the equality subgraph, update potentials when stuck — maintains the duality invariants throughout. Implementing the algorithm in Coq with a well-founded termination measure and proving each step preserves the invariants is mechanical but lengthy (~1500-2500 lines).

2. **Hoeffding's lemma (convexity of exp).** The Hoeffding tail bound in Part XXV takes the sub-Gaussian MGF inequality `E[exp(λ(X-μ))] ≤ exp(λ²(b-a)²/8)` for `X in [a,b]` as a hypothesis. A complete proof needs convexity of `exp`, which Stdlib provides only at the derivability level (`derive_pt_exp`); the convexity lemma itself follows from the second-derivative test (or Taylor remainder) plus the MVT, both of which are in Stdlib but require several hundred lines to compose. With Hoeffding's lemma proved, `hoeffding_optimized_lambda` directly produces the standard tail bound for sums of bounded iid random variables.
