# Remaining work

All listed items closed.

The optimal-matching pipeline now ships in three forms with full parametric correctness:

  - Part XIX `brute_match`: constructive O(n!) optimum via permutation enumeration; `brute_match_optimal_among_perms` proves optimality among reordering-derived matchings.
  - Part XXII `dp_max_match`: canonical bipartite-assignment DP recurrence with `dp_max_match_eq_brute_weight` proving its weight equals `brute_match`'s under `NoDup gts`. With extraction-time memoization, runtime is O(2^n · n²).
  - Part XXIII LP-duality theorem `hungarian_optimal_via_duality`: a perfect matching M with dual-feasible / complementary-slack potentials (u, v) is optimal among perfect matchings. The classical sum-of-potentials argument carried out via `Permutation`-based perfect-matching predicates and elementary list-sum manipulation; no LP-polytope vertex theory or unimodularity required.

A strict-O(n³) Hungarian implementation is the natural follow-up engineering step. With Part XXIII's duality theorem in place, correctness reduces to showing that the algorithm maintains dual feasibility (u_b + v_g ≥ cost b g) and complementary slackness (u_b + v_g = cost b g for matched pairs) throughout its iterations — a structural invariant rather than a deep LP-theoretic property.
