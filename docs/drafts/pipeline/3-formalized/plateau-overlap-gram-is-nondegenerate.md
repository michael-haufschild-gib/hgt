# Every finite plateau overlap Gram is positive definite

- **ID:** plateau-overlap-gram-is-nondegenerate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every positive width, a nonzero finite coefficient vector synthesizes
  a nonzero plateau test with strictly positive squared mass. Its full autocorrelation
  Gram quadratic form is strictly positive.
- **Module:** `TransMetzlerWeilPositivity/ThePlateauOverlapGramIsNondegenerate.lean`.

## Proof

Choose the least index `n` with a nonzero coefficient. Evaluate immediately to the right
of `log n`, at distance less than both the profile width and the next logarithmic gap.
All earlier coefficients vanish, while all later atoms vanish by support. The remaining
term is nonzero because the plateau is strictly positive on `(0,1)`.

The synthesized test is continuous and compactly supported. Its nonnegative square is
nonzero at that point, so its integral is positive. The exact autocorrelation expansion
identifies this integral with the full Gram quadratic form, including every overlap entry.

This is finite-dimensional nondegeneracy at each width and horizon. It supplies no lower
bound uniform in these parameters and no sign for the complete Weil form.

## Lean declarations

- `plateau_atomicTest_ne_zero`
- `integral_plateau_atomicTest_sq_pos`
- `plateau_overlap_gram_strictly_positive`

Direct `lake --old env lean` check and all three transitive axiom audits passed with default
limits. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired.
