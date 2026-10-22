# Hedenmalm projective Rayleigh-gap universality law

## Status

Lean-formalized; exact file audit passed on 2026-07-22. Literature novelty audit pending.

## Corpus sources

- `RHTower/HedenmalmRankTwoTangentInertia.lean`
- `RHTower/RayleighProjectiveQuantumFisher.lean`

## Theorem-first derivation

The first source proves linear independence of the actual exponentially tilted theta source and
its aperture tangent in complex `L²(ℝ)`. The second source proves a generic spectral-gap bound for
projective Gram/Fisher tangent energy. Normalizing the concrete pair discharges every geometric
hypothesis of the generic theorem.

## Universal law

For every `|a| < 1`, every symmetric continuous operator having the normalized Hedenmalm source as
an eigenvector and satisfying positive-gap coercivity on the normalized aperture tangent obeys

1. strictly positive concrete projective Gram/Fisher tangent energy;
2. the quantitative bound by Rayleigh excess divided by gap; and
3. strict Rayleigh separation of tangent energy above the source eigenvalue.

The third conclusion is forced by the first two and positive gap; it was not stated in either
parent module.

## Lean status

- Module: `GaloisForLFunctions.RHTower.HedenmalmProjectiveRayleighGapUniversalityLaw`
- Capstone: `RHTower.thetaCuspRightLine_projectiveRayleighGap_strict`
- Exact command passed: `lake env lean GaloisForLFunctions/RHTower/HedenmalmProjectiveRayleighGapUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
