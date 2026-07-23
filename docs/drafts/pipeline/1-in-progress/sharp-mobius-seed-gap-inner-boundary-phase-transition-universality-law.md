# Sharp Möbius seed-gap inner/boundary phase-transition universality law

- **ID:** sharp-mobius-seed-gap-inner-boundary-phase-transition-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of Route-B two-field inner-row cancellation, singleton-window
  seed-gap arithmetic, prime-packet interval rigidity, and Möbius squarefree support
- **Statement:** For every smooth row `2 ≤ d ≤ y`, sharp Möbius weights annihilate all inner
  `d·p ≤ N` coefficients, while every singleton-window boundary coefficient equals `μ(d)`; on
  every nonempty vertical interval, a nonempty boundary packet has positive energy exactly when
  `d` is squarefree.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit pending

## Corpus inputs

- `inner_row_vanishes_sharp`
- `not_rough_of_smooth_divisor`
- `seedGapCoeff_eq_lam_of_singleton_boundary`
- `seedGap_boundary_component_secondMoment_pos_iff`
- `ArithmeticFunction.moebius_ne_zero_iff_squarefree`

## Proof

`[PROVED HERE]` Fix `2 ≤ d ≤ y`.  For a prime `p > y` in the inner range `d p ≤ N`,
the two-field sharp-design theorem identifies the complete divisor-window coefficient with the
Möbius divisor sum and makes it zero.  Since `d` is a nontrivial `y`-smooth divisor of `p d`, that
integer is not `y`-rough, so the rough-seed subtraction is also zero.  Hence the actual seed-gap
coefficient vanishes.

In the singleton-window boundary range `p ≤ N < p minFac(d)`, the seed-gap boundary theorem gives
the exact coefficient `μ(d)`.  For any nonempty finite boundary-prime packet, the interval
prime-packet theorem says its energy is positive exactly when this coefficient is nonzero.
Möbius nonvanishing is equivalent to squarefreeness of `d`.  No computation is used.

## Strict gain over corpus endpoints

The two-field theorem proves only inner cancellation and does not describe what appears beyond the
window.  The seed-gap theorem proves a generic boundary coefficient but does not compare it with
the same sharp row’s inner phase or identify its arithmetic support.  Their closure gives an exact
rowwise phase transition and classifies observable boundary survival by squarefreeness.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.SharpMobiusSeedGapInnerBoundaryPhaseTransitionUniversalityLaw`
- Main theorem:
  `sharpMobiusSeedGap_innerBoundaryPhaseTransitionUniversality`
- Source:
  `formal/GaloisForLFunctions/RHTower/SharpMobiusSeedGapInnerBoundaryPhaseTransitionUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/SharpMobiusSeedGapInnerBoundaryPhaseTransitionUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the paper proof.  Post-proof audit begins only after exact
Lean verification.

## Log

- 2026-07-23 — Fresh terminal-pair scan exposed Route-B inner cancellation and boundary survival
  as two ends of one rowwise mechanism.
- 2026-07-23 — Dependency-closed proof completed from five existing Lean endpoints.
- 2026-07-23 — Exact theorem formalized, checked warning-free, and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof web search attempted; search service returned invalid-response errors, so
  collision audit remains open.
