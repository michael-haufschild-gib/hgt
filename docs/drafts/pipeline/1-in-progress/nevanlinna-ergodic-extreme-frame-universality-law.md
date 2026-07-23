# Nevanlinna ergodic/extreme/frame universality law

Status: paper proof complete; Lean exact audit passed.

## Lean sources

- `nevBauer_extreme_iff`
- `barycenter_isErgodicConstraintStationaryLaw_iff_dirac`
- `barycenter_support_infinite`
- `injective_completeBoundaryCanonicalFrameTower`

## Survivor

For the canonical Nevanlinna boundary of every normalized positive Hamburger moment sequence with
bounded kernel, invariant-set ergodicity and convex extremality select exactly the same Dirac
leaves. Every infinite-support projective mixture is therefore nonergodic and nonextreme, but its
real carrier still has infinite support and its complete inverse-Cholesky frame tower uniquely
recovers the projective parameter law.

This joins three previously separate structures on the same canonical boundary: Markov-kernel
ergodicity, Bauer-simplex geometry, and complete-frame observability.

## Proof skeleton

Both ergodicity and extremality are equivalent to the parameter law being Dirac. An
infinite-support law cannot be Dirac. Exact projective-label recovery transports infinite support
to its barycenter, while injectivity of the complete frame tower supplies the final observability
statement.

## Novelty audit

Pending post-formalization literature search.
