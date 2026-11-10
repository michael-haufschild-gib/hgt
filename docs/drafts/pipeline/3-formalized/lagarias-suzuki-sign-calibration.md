# Lagarias–Suzuki sign calibration

- **Stage:** 3-formalized
- **Source:** review-0911 §11.3.

For `Y≥1`, the completed Eisenstein constant term
`Λ(2s)Y^s+Λ(2s−1)Y^(1−s)` has no non-real zero off `Re s=1/2`.
The pole-cleared function has at most one zero right of that line.
Real exceptional zeros are allowed.

Its two entire halves have a Schur quotient on the right half-plane.
The pole contributes index one. Conjugation therefore forces an
exceptional zero to be real; the functional equation gives the left half.

Lean: `InfiniteRankPurityTheory/TheEisensteinConstantTermIsPureByParity.lean`,
`lineLaw`, `constantTerm_zero_subsingleton`. Direct audit passed;
both transitive axiom lists contain only `propext`, `Classical.choice`,
`Quot.sound`. Both review-0911 obstacle ledgers include this calibration.
