# Remaining work

1. Theorem numbering inside section comments restarts per
   section. Headers like "Theorem 1." through "Theorem 3." in
   `MultiClassL`, `SGDDescentVec`, `DETREquilibriumMargin`, and
   others are local indices that look like global ones; the file
   has hundreds of `Theorem`s and `Corollary`s and these local
   numbers are not stable cross-reference targets. Closable by
   dropping the inline numbering.
