# Remaining work

1. Rademacher complexity and true PAC generalization. The current
   substitute is `massart_finite_class_bound` /
   `massart_uniform_deviation`, which is standard for finite
   hypothesis classes. Promoting to the infinite-class continuous
   form requires probability machinery that Stdlib does not
   provide; would need to depend on or build out a probability
   theory library.

2. Remove the `cost_nonneg` hypothesis from
   `bitmask_optimal_eq_brute_weight`. The hypothesis is forced by
   `mask_max_R_aux`'s base case returning `0`: when contributions
   are negative, the `fold_right Rmax 0` form differs from
   `dp_max_match`'s `Rmax_list (head) (...)` init form. Removable
   by restructuring `mask_max_R_aux` to mirror `dp_max_match`'s init
   (or by using `option R` and a saturating max).

3. IEEE 754 subnormal-range encoder and round-trip. Normal-range
   has the full chain `b64_encode_normal` →
   `b64_encode_normal_well_formed` → `b64_encode_decode_close`.
   Subnormal range has `b64_subnormal_quantize` and
   `b64_subnormal_bounded_error` only. The encoder/round-trip
   extension is mechanically similar to the normal-range proof.

4. Formal complexity bound on `bitmask_dp`. The `O(n * 2^m * m)`
   runtime is structurally evident from the `Fixpoint` form but
   not proved as a Coq-level resource bound. Coq cost-modeling is
   nonstandard; either CoqEval or a hand-rolled step counter would
   be needed.
