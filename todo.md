# Remaining work

All listed items closed at the correctness level.

Optimal bipartite weighted matching ships in two flavors with full parametric correctness proofs:

  - Part XIX: `brute_match` — constructive O(n!) optimum via permutation enumeration, with `brute_match_optimal_among_perms` proving optimality among reordering-derived matchings.
  - Part XXII: `dp_max_match` — standard bipartite-assignment DP recurrence with `dp_max_match_eq_brute_weight` proving its weight equals `brute_match`'s weight under `NoDup gts`. Standard memoization at extraction time gives O(2^n · n²) runtime.

The strict-polynomial O(n³) Hungarian variant with potentials, alternating trees, and augmenting paths is an asymptotic improvement target; its correctness proof requires LP duality on the assignment polytope (or Berge's theorem on the equality subgraph), neither of which is in Stdlib. For realistic instance sizes (DETR query slots of order 10–20), the O(2^n · n²) DP is sufficient.
