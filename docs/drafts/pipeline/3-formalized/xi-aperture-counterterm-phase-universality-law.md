# Xi aperture counterterm phase universality law

- **ID:** xi-aperture-counterterm-phase-universality-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** closure of `XiAperturePoissonFullApertureHilbertTransport`, `XiApertureResponseGainPrimeRenormalization`, and `XiApertureResponseCorrelationDet2`
- **Statement:** After subtracting the unit background only at aperture one, the fused all-prime gain admits a summable scalar prime-harmonic renormalization at every positive integral aperture for one coefficient only: `6` at `a=1`, and `0` at every `a≥2`.

## Goal

Replace separate unit-boundary and deep-aperture summability statements by one sharp all-depth
classification of the renormalization coefficient.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [x] 2 → 3  formalized: exact Lean theorem, direct elaboration, final module build, lint, and axiom audit pass
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

At `a=1`, use the existing iff that uniquely identifies coefficient `6`.  If `a≠1`, positivity
forces `a≥2`, so the raw gain is summable.  If subtracting `c/p` also leaves a summable family,
their difference makes `c/p` summable.  Prime-harmonic divergence forces `c=0`; conversely zero
coefficient leaves the already-summable deep gain.

## Audit

- **[CORPUS]:** unit aperture uniquely requires coefficient `6`
- **[CORPUS]:** every positive depth `a≥2` has summable raw squared gain
- **[CORPUS]:** no theorem classifies the unique counterterm simultaneously across all depths
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; the boundary jump `6→0` is not packaged or stated elsewhere
- **Status:** `[PAPER-PROVED] [EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — all-depth unique-counterterm theorem extracted from exact unit and deep phases
- 2026-07-22 — exact development check passed with `lake env lean GaloisForLFunctions/RHTower/XiApertureCountertermPhaseUniversalityLaw.lean`
