# Every fixed Xi Jensen degree is eventually real-rooted

- **ID:** every-fixed-xi-jensen-degree-is-eventually-real-rooted
- **Stage:** 3-formalized
- **Statement:** For every natural degree `d`, the actual Xi Jensen polynomial
  `J^(d,n)` splits over the reals for all sufficiently large shifts `n`.

## Proof

The proved affine-normalized Jensen polynomials converge at every real point
to the probabilists' Hermite polynomial `He_d`. Its `d` simple roots admit
disjoint intervals with strictly opposite endpoint signs. Convergence at
the finitely many endpoints preserves every sign change. The intermediate
value theorem supplies `d` distinct real roots, and the normalized polynomial
has degree at most `d`, so all roots are real. Its normalizing constant is
nonzero and its affine substitution has nonzero slope. Undoing these changes
preserves splitting and proves the claim for the actual Jensen polynomial.

## Scope

Every fixed degree is covered. The shift threshold is existential; no uniform
threshold in unbounded degree and no all-shift assertion is claimed.

## Verification

`RHTower/Jensen/EveryFixedDegreeIsEventuallyRealRooted.lean`:
`eventually_splits_xiJensenHermitePolynomial` and
`eventually_splits_xiJensenPoly` passed their direct `lake --old env lean`
check and transitive axiom audits (`propext`, `Classical.choice`, `Quot.sound`).
Umbrella import wired.
