# Remaining work

1. IEEE 754 subnormal-range encoder and round-trip. Normal-range
   has the full chain `b64_encode_normal` →
   `b64_encode_normal_well_formed` → `b64_encode_decode_close`.
   Subnormal range has `b64_subnormal_quantize` and
   `b64_subnormal_bounded_error` only. The encoder/round-trip
   extension is mechanically similar to the normal-range proof.

2. Formal complexity bound on `bitmask_dp`. The `O(n * 2^m * m)`
   runtime is structurally evident from the `Fixpoint` form but
   not proved as a Coq-level resource bound. Coq cost-modeling is
   nonstandard; either CoqEval or a hand-rolled step counter would
   be needed.

3. Worked instances are small or partly vacuous. `c40_D`, `c30_D`,
   and `c1_D` are 2-element lists; the matrix-based examples
   (`e20_M`, `arch_M1` / `arch_M2`, `ibp_dead_M1` / `ibp_dead_M2`,
   `example_M`) are all 1x1. `e20_separated_at_slack_one`, the
   largest detection batch with 20 elements, holds vacuously
   because `c1_iou` returns 60 on every distinct nat-box pair
   while `tau = 70`, so the `[tau <= iou]` branch of `Separated`
   is never reached. `c11_box1` / `c11_box2` (overlapping
   rectangles), `c20_m1` / `c20_m2` (3-column bitmap masks), and
   `c23_bitmap1` / `c23_bitmap2` (2x3 bitmap detections) are
   non-trivial geometric/bitmap witnesses but still small.
   Closable by adding one or more instances combining realistic
   dimensionality, a genuinely fired high-IoU pair, and a
   non-identity Lipschitz score head.

4. `matching_injective` name collision. In `DETRMatchingDerived`
   the identifier is a `Hypothesis` on a function `Box -> GT`; in
   `HungarianMatching` it is a `Definition` on a `list (Box * GT)`
   formed as the conjunction of `matching_box_injective` and
   `matching_gt_injective`. Both modules concern matching, so
   module qualification only partially disambiguates. Closable by
   renaming the function-shaped version to `matched_gt_injective`.

5. Theorem numbering inside section comments restarts per
   section. Headers like "Theorem 1." through "Theorem 3." in
   `MultiClassL`, `SGDDescentVec`, `DETREquilibriumMargin`, and
   others are local indices that look like global ones; the file
   has hundreds of `Theorem`s and `Corollary`s and these local
   numbers are not stable cross-reference targets. Closable by
   dropping the inline numbering.
