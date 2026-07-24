# Xi even-shift archimedean-curvature cocycle universality law

- **ID:** xi-even-shift-archimedean-curvature-cocycle-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the completed-zeta two-step curvature response and the
  arbitrary even Xi prime-correction telescope
- **Statement:** For every even translation `s ↦ s+2m`, the completed-zeta archimedean curvature
  defect is the sum of the translated two-step rational responses and is exactly the derivative
  of the arbitrary-even Xi prime correction.  These responses obey the additive translation
  cocycle law.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `completedZetaArchimedeanCurvature_add_two_sub`
- `completedZetaArchimedeanShiftRational`
- `xiEvenShiftPrimeCorrection`
- `xiEvenShiftPrimeDefect_telescope`
- `HTGeometry.trigamma_add_nat`

## Proof

`[PROVED HERE]` Define the order-`m` curvature response as

`R_m(s) = ∑_{j<m} completedZetaArchimedeanShiftRational(s+2j)`.

Summing the existing two-step identity at `s,s+2,…,s+2(m-1)` telescopes to

`completedZetaArchimedeanCurvature(s+2m)
  - completedZetaArchimedeanCurvature(s) = R_m(s)`.

Each summand of `xiEvenShiftPrimeCorrection m` is
`1/(s+2j+2) + 1/(s+2j+1) - 1/(s+2j-1)`.  On `Re(s)>2` all denominators are nonzero, and direct
differentiation gives exactly
`completedZetaArchimedeanShiftRational(s+2j)`.  Finite summation therefore gives
`(xiEvenShiftPrimeCorrection m)'(s) = R_m(s)`, proving equality with the curvature defect.
Splitting the finite sum at `m` gives
`R_{m+n}(s)=R_m(s)+R_n(s+2m)`, the translation cocycle law.  No computation is used.

## Strict gain over corpus endpoints

The completed-zeta curvature endpoint treats only one shift by two.  The even Xi endpoint gives
an arbitrary-shift correction at logarithmic-derivative level but does not identify its
derivative.  Their closure proves an all-even curvature law, identifies the correction derivative
with the genuine archimedean curvature defect, and exposes the exact response cocycle.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiEvenShiftArchimedeanCurvatureCocycleUniversalityLaw`
- Main theorem:
  `xiEvenShiftPrimeCorrection_deriv_eq_archimedeanCurvatureDefect`
- Source:
  `formal/GaloisForLFunctions/RHTower/XiEvenShiftArchimedeanCurvatureCocycleUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/XiEvenShiftArchimedeanCurvatureCocycleUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
completed-zeta archimedean curvature, arbitrary even translations, trigamma corrections, and
translation cocycles found no exact collision.  Closest inspected primary sources address
different completed-zeta structures:

- S. Sekatskii, *Analysis of Voros criterion: what derivatives involving the logarithm of the
  Riemann xi-function at z=1/2 should be non-negative for the Riemann hypothesis holds true*,
  <https://arxiv.org/abs/1407.5758>, studies high derivatives of `log ξ` at the symmetry point,
  not finite even translations or the derivative of a prime correction.
- F. Brown, *A multi-variable version of the completed Riemann zeta function and other
  L-functions*, <https://arxiv.org/abs/1904.00190>, develops multivariable completions and
  functional equations but not this one-variable all-even rational curvature cocycle.

## Log

- 2026-07-23 — Corpus-defined-symbol scan exposed the all-even trigamma/Xi-correction closure.
- 2026-07-23 — Dependency-closed telescoping and differentiation proof completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
