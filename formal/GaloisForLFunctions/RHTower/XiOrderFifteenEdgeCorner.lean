import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-fifteen squared-Xi source

For a Xi zero with centered coordinates `delta + gamma*I`, the order-fifteen radial atom is
controlled by the sixteenth reciprocal power of

`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

This module sharpens the rational sector certificate from coefficient `100` to `104`.  At every
`y > 1/4`, failure of that certificate forces an off-critical zero into the compact corner

`1/5 < delta^2 < 1/4`, `85 < gamma^2 < 104`.

The proof is unconditional and uses no zero table.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/104` has a
strictly positive sixteenth reciprocal power. -/
theorem orderSixteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 104 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 16).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 981 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

/-- Off the critical line, the central four-fifths of the critical strip satisfies the rational
order-sixteen sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSixteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 5 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 104) (u₀ := 1 / 5)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Every Xi zero above squared height `104` satisfies the rational order-sixteen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSixteenSectorRatio_of_oneHundredFour_le_im_sq
    (q : XiZeroCopy) (hhigh : 104 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 104)
    (u₀ := 1 / 4) (v₀ := 104) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

/-- If an off-critical Xi zero fails the order-sixteen sector certificate at `y > 1/4`, then it
lies in the exact compact edge corner `1/5 < delta^2 < 1/4`, `85 < gamma^2 < 104`. -/
theorem xiOrderSixteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 104 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderSixteenSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderSixteenSectorRatio_of_oneHundredFour_le_im_sq q h hy) hfail

/-- A nonpositive sixteenth reciprocal-power atom from an off-critical Xi zero at `y > 1/4`
must lie in the exact compact edge corner. -/
theorem xiOrderSixteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 16).re ≤ 0) :
    (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 104 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderSixteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiOrderSixteenSectorFailure_mem_edgeCorner q hoff hy) hnonpos

end

end RHTower
