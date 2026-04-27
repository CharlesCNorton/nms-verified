# Remaining work

1. `matching_injective` name collision. In `DETRMatchingDerived`
   the identifier is a `Hypothesis` on a function `Box -> GT`; in
   `HungarianMatching` it is a `Definition` on a `list (Box * GT)`
   formed as the conjunction of `matching_box_injective` and
   `matching_gt_injective`. Both modules concern matching, so
   module qualification only partially disambiguates. Closable by
   renaming the function-shaped version to `matched_gt_injective`.

2. Theorem numbering inside section comments restarts per
   section. Headers like "Theorem 1." through "Theorem 3." in
   `MultiClassL`, `SGDDescentVec`, `DETREquilibriumMargin`, and
   others are local indices that look like global ones; the file
   has hundreds of `Theorem`s and `Corollary`s and these local
   numbers are not stable cross-reference targets. Closable by
   dropping the inline numbering.
