# Critical-Mellin four-coordinate collapse universality law

## Status

Lean-formalized; exact file audit passed on 2026-07-22. Literature novelty audit pending.

## Corpus sources

- `RHTower/CCM/CCMComplexMellinColligation.lean`
- `RHTower/PolarPrimeChannelContinuation.lean`
- `RHTower/XiCriticalMellinSourceFactorization.lean`
- `RHTower/CCM/CCMInverseTiltedCriticalMellinFactorization.lean`

## Theorem-first derivation

These modules independently expose four critical-Mellin coordinates. Exact source formulas show
that the polar complex carrier and canonical continued defect agree globally. Existing pairwise
right-half-plane identities then collapse the complex Laplace channel and pole-filled
inverse-tilted defect onto the same value.

## Universal law

On `Re u > 0`, all four coordinates coincide. For any finite packet of positive real-part complex
nodes, the CCM critical-Mellin Gram is therefore exactly the Gram of
`regularizedCriticalMellinDefect`. The Cauchy incidence decomposition can use that regularized germ
directly—the same germ whose holomorphy on `Re u > -1/2` is the corpus RH classifier.

## Lean status

- Module: `GaloisForLFunctions.RHTower.CriticalMellinFourCoordinateCollapseUniversalityLaw`
- Capstone: `RHTower.cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_regularizedCriticalMellin`
- Exact command passed: `lake env lean GaloisForLFunctions/RHTower/CriticalMellinFourCoordinateCollapseUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
