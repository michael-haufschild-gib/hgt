# Hadamard sign near the line at typical heights

- **ID:** HADAMARD-TYPICAL-HEIGHT
- **Stage:** 3-formalized
- **Type:** DENSITY THEOREM (route LA, F0242 receiver; exponential upgrade of the `1 − O(1/c)` critical-scale proportion)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 65
- **STATUS:** MUST-594
- **Companion:** `speiser-typical-height-density.md` (MUST-593, the left mirror)

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/XiHadamardSignTypicalHeight.lean` (wired, clean, standard axioms).

1. `xi_ne_zero_and_re_logDeriv_pos_rightBox`. Suppose `ZetaLogDerivScaleData t R B` holds with
   `0 < R ≤ 1/16`. Take `s` in the right box `1/2 + 3R/4 ≤ Re s ≤ 1/2 + 6R`, `|Im s − t| ≤ 6R`, with
   `Im s > 0` and `B < stripFloor (Re s) (Im s)`. Then `ξ(s) ≠ 0` and `Re(ξ'/ξ)(s) > 0`.
2. `exists_volume_hadamardSign_fail_near_line_le`. There are `C, c > 0` such that for every `κ` and
   all large `T`,
   `|{t ∈ [T,2T] : ∃ s, 1/2 + κ/log T ≤ Re s ≤ 3/4, |Im s − t| ≤ κ/log T, ¬(ξ(s) ≠ 0 ∧ Re(ξ'/ξ)(s) > 0)}| ≤ C T e^{−cκ}`.

## Mechanism

- `ξ = archFactor · ζ` on the strip, so `ξ'/ξ = archFactor'/archFactor + ζ'/ζ`.
- `Re archFactor'/archFactor ≥ stripFloor σ τ ≥ ½ log(τ/2π) − 1/25` (`stripWindingRate_ge`,
  `stripFloor_ge_half_log_sub`). With `B = 10^{−9} log T`, the ζ part cannot cancel it.
- The dyadic grid pinned at `R = 1/24`, the covering lemma and the summation are shared with MUST-593
  (`speiser_grid_facts`, `exists_speiser_grid_scale`, `volume_speiser_scales_le`).

## Relation to the corpus

- `exists_volume_hadamardFail_criticalScale_le` (R:ZetaCriticalScaleTailMoment) gives failing measure
  `≤ 2(D/c)(T₂ − T₁) + O(log²U)` on the single line `σ = 1/2 + c/log U`, i.e. proportion `1 − O(1/c)`.
- The new bound is `e^{−c'κ}`, uniform over the whole band `1/2 + κ/log T ≤ σ ≤ 3/4`, and localized
  to `κ/log T`-neighbourhoods of the height.
- Together with MUST-593, outside heights of density `C e^{−cκ}` the band `κ/log T ≤ |Re s − 1/2| ≤ 1/4`
  has the Hadamard sign on the right and `ζ' ≠ 0` on the left.

## Limits

- The failure density is never zero. The exceptional heights are scale-data failures, controlled
  only by near-line zero concentration.
- An off-line zero at distance `a/log T` spoils the Hadamard sign in its rectangle regardless of `κ`
  once `κ < a`. Density one at fixed `κ` is the NLC problem.
