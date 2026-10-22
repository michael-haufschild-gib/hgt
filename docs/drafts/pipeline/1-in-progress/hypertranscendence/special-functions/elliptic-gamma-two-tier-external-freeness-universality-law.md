# Elliptic-Gamma two-tier external-freeness universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.HTGeometry.EllipticGammaTwoTierExternalFreenessUniversalityLaw`

## Theorem-generated route

Source statements were read first:

- `ellipticGammaExternalQuotientFamily_differentialMatroid_eq_freeOn_rationalBase`
- `ellipticGammaExternalDifferentialFamilySum_ne_ellipticFraction_of_nonzero`
- `thetaTranslationNontorsion_of_ellipticGammaSourcePeriods_linearIndependent`

All statements use the same rank-three period packet and the same nonresonant separated external
translations.  The first sees nonlinear differential freeness over the rational coordinate base.
The second survives coefficient enlargement in a different direction: no nonzero linear
differential combination enters the elliptic fraction field.

## Candidate law

Separated elliptic-Gamma translations have a two-tier external freeness: free differential
matroid over `ℂ(z)` and differential-operator atomicity against elliptic fractions.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
