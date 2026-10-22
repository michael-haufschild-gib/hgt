# Elliptic-Gamma commensurable reflection-factorization universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/EllipticGammaInversion.lean`
  - `ellipticGammaProduct_reflection`
- `HTGeometry/EllipticGammaProductCommensurableFactorization.lean`
  - `ellipticGammaProduct_additivePeriod_factorization`

## Universal law

For every pair of additively commensurable elliptic periods, the finite residue-class family
product produced by Felder–Varchenko flattening is inverted exactly when its additive coordinate is
reflected from `z` to `σ - z`. Hence commensurable factorization and elliptic-Gamma unitarity
commute without extra convergence or nonvanishing hypotheses.

## Paper proof

Factor the elliptic-Gamma product at `z` and again at `σ - z` using the same period congruence.
The elliptic-Gamma reflection theorem identifies the second product with the inverse of the first.
Substitute the two exact family factorizations.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/EllipticGammaCommensurableReflectionFactorizationUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/EllipticGammaCommensurableReflectionFactorizationUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
commensurable family factorization and product reflection separately but no commuting
reflection-factorization law for the finite family product.
