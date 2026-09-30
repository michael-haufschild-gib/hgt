# Speiser's criterion at typical heights

- **ID:** SPEISER-TYPICAL-HEIGHT
- **Stage:** 3-formalized
- **Type:** DENSITY THEOREM (unconditional partial producer for Speiser's criterion)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 64
- **STATUS:** MUST-593

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/SpeiserTypicalHeightDensity.lean` (wired, clean, standard axioms).

1. `riemannZeta_ne_zero_and_deriv_ne_zero_leftBox`. Suppose `ZetaLogDerivScaleData t R B` holds with
   `0 < R ≤ 1/24` and `t ≥ 101`. Then every `s` in the mirrored left box
   `1/2 − 6R ≤ Re s ≤ 1/2 − 3R/4`, `|Im s − t| ≤ 6R` with `B + 1 < log(Im s/2π)` has
   `ζ(s) ≠ 0` and `ζ'(s) ≠ 0`.
2. `exists_volume_deriv_riemannZeta_eq_zero_leftBox_le`. This is the one-scale density: the bad
   heights have measure `≤ C T(2e^{−κ/120000} + κ²e^{−κ/16} + e^{−κ/30}) + C T^{1/2}`, where
   `κ = R log T`.
3. `exists_volume_deriv_riemannZeta_eq_zero_near_line_le`. There are `C, c > 0` such that for every
   `κ` and all large `T`,
   `|{t ∈ [T,2T] : ∃ s, ζ'(s) = 0, 1/4 ≤ Re s ≤ 1/2 − κ/log T, |Im s − t| ≤ κ/log T}| ≤ C T e^{−cκ}`.

## Mechanism

- **Reflection.** `ζ'/ζ(s) = χ'/χ(s) − ζ'/ζ(1 − s)`, via `logDeriv_riemannZeta_add_reflect_of_strip`
  and `logDeriv_zetaChi_off_poles`. The point `1 − s̄` lies in the right box, so
  `|ζ'/ζ(1 − s)| ≤ B` by conjugation symmetry.
- **Slope.** On the critical line, `χ'/χ` equals `−2θ'(t)`
  (`logDeriv_zetaChi_displacedLinePt_zero_eq`), and `θ'(t) ≥ ½log(t/2π) − O(1/t)`. A horizontal
  displacement `d ≤ 1/4` costs `O(1/t)`. Together these give `Re χ'/χ(s) ≤ −log(Im s/2π) + 1`
  (`re_logDeriv_zetaChi_displaced_le`). So `Re ζ'/ζ(s) < 0`, and hence `ζ'(s) ≠ 0`.
- **Density.** Apply the exponential scale-data theorem (`exists_volume_not_zetaLogDerivScaleData_le_exp`)
  with `B = 10^{−9} log T`, on the dyadic grid `R_j = 2^{j−J}/24`, `j ≤ J`. Its windows
  `[3R_j/4, 6R_j]` tile `[κ/log T, 1/4]` (`speiser_grid_facts`, `exists_speiser_grid_scale`). The
  summation over the grid is `volume_speiser_scales_le`.

## What it says

Speiser: RH ⇔ `ζ'` has no zeros in `0 < Re s < 1/2`. Unconditionally, a zero of `ζ'` at distance
`≥ κ/log T` left of the line, up to distance 1/4, can occur only at heights of relative density
`≤ C e^{−cκ}`. These are exactly the heights where the right-side log-derivative box fails. Such a
failure needs a zero of `ζ` within `O(κ/log T)` to the right of the line, or a large Dirichlet
polynomial.

## Limits and residual

- The density does not reach zero. The exceptional heights are the scale-data failures, whose
  measure is controlled only by the near-line zero concentration (the common residual of the
  LA/TG/WD receivers).
- The range `Re s < 1/4` is not covered. The displacement bound for `χ'/χ` is used only for `d ≤ 1/4`.
- Distance `< κ/log T` is the Levinson–Montgomery regime. There RH predicts only zeros of `ζ'`
  exactly on or right of the line, and the box method gives nothing below one scale unit.
