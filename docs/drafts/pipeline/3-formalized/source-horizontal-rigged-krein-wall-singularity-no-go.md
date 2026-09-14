# Source-horizontal rigged Krein wall-singularity no-go

- **ID:** source-horizontal-rigged-krein-wall-singularity-no-go
- **Stage:** 3-formalized
- **Route:** shared HB / FZZ-P / RBH / PW-B source-polarization producer
- **Module:** `GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinWallSingularityNoGo`
- **Capstone:** `sourceHorizontalWallRegularRiggedKreinCompletionRouteKilled`

## Result

The canonical all-prime source-selected fundamental symmetry acts on one fixed nonzero two-prime
time axis by `-1` on the left half-strip, `+1` on the right half-strip, and `0` on the critical
wall. No alternative wall value yields a continuous path agreeing with both open chambers.

## Route consequence

This kills every regular-global completion of this canonical rigged-Krein polarization, already in
the weak pointwise topology detected by one fixed source vector. Any surviving completion feeding
phase-sensitive BM darkness must be genuinely critical-wall singular or sheet-changing; allowing
unbounded operators or infinite index without such wall behavior is insufficient.

## No-go closure

- **Exact killing mechanism:** left and right source chambers force distinct limits `-e` and `e`
  for a nonzero source axis `e`.
- **Strongest positive survivor:**
  `preDivisorRiggedPrimeFundamentalSymmetry_timeAxis_chambers` gives the exact `-e / 0 / e`
  classification.
- **New insight:** obstruction is a critical-wall jump, not failure of nuclearity, positivity, or
  finite rank.
- **Status:** paper proof dependency-closed; both statements formalized in Lean.

## Novelty audit through 2026-08-31

Corpus search found chamberwise polarization and fibre trivialization but no two-sided wall-extension
classification. External searches found general fixed-symmetry continuous-frame and bounded-metric
theory, not this source-specific wall jump: [Carrillo--Esmeral--Wagner](https://arxiv.org/abs/2103.12267),
[Mostafazadeh](https://arxiv.org/abs/quant-ph/0606173).

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinWallSingularityNoGo.lean`
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinWallSingularityNoGo`
- imported by `GaloisForLFunctions/RHTower.lean`
