# Polar-prime aperture--Poisson conservation universality law

## Status

Lean-formalized; exact file audit passed on 2026-07-22. Literature novelty audit pending.

## Corpus sources

- `RHTower/PolarPrimeChannelContinuation.lean`
- `RHTower/XiAperturePoissonEulerLogDerivCompletion.lean`
- `RHTower/XiRelativeResolventFlux.lean`

## Theorem-first derivation

The critical Mellin-defect channel contains `ζ'/ζ(a)` plus the two rational polar terms
`1/(a-1)` and `1/a`. Independently, complete prime-valuation fusion reconstructs the aperture
current `-a ζ'/ζ(a)`. Matching the shift and multiplying the first channel by `a` makes all
arithmetic prime data cancel.

## Universal law

For every real aperture `a > 1`:

1. `a · criticalMellinDefect(a-1) + clockedPrimeCurrent(a) = a/(a-1) + 1`;
2. after archimedean completion, the remainder subtracts exactly `a logDeriv(archFactor)(a)`;
3. dividing by `a` identifies the shifted critical channel minus `logDeriv xi(a)` with the
   prime-blind rational/archimedean boundary current.

No parent module states this cancellation or the direct critical-Mellin/Xi residual identity.

## Lean status

- Module: `GaloisForLFunctions.RHTower.PolarPrimeAperturePoissonConservationUniversalityLaw`
- Capstone: `RHTower.criticalMellinDefect_sub_xiLogDeriv_eq_primeBlindArchBoundary`
- Exact command passed: `lake env lean GaloisForLFunctions/RHTower/PolarPrimeAperturePoissonConservationUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
