import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-sixteen squared-Xi source

For a Xi zero with centered coordinates `delta + gamma*I`, the order-sixteen radial atom is
controlled by the seventeenth reciprocal power of

`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

The rational sector coefficient `118` protects the central band `delta^2 <= 9/50` and every
zero above squared height `118`.  Thus, at every `y > 1/4`, failure of that certificate forces
an off-critical zero into the compact corner

`9/50 < delta^2 < 1/4`, `85 < gamma^2 < 118`.

The proof is unconditional and uses no zero table.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/118` has a
strictly positive seventeenth reciprocal power. -/
theorem orderSeventeenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 118 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 17).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 923 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

/-- Off the critical line, the protected central band satisfies the rational order-seventeen
sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (9 / 50 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 118) (u₀ := 9 / 50)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Every Xi zero above squared height `118` satisfies the rational order-seventeen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq
    (q : XiZeroCopy) (hhigh : 118 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 118)
    (u₀ := 1 / 4) (v₀ := 118) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

/-- Failure of the order-seventeen sector certificate at `y > 1/4` forces an off-critical Xi
zero into `9/50 < delta^2 < 1/4`, `85 < gamma^2 < 118`. -/
theorem xiOrderSeventeenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 118 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderSeventeenSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq q h hy) hfail

/-- A nonpositive seventeenth reciprocal-power atom at `y > 1/4` must lie in the compact edge
corner. -/
theorem xiOrderSeventeenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 17).re ≤ 0) :
    (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 118 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiOrderSeventeenSectorFailure_mem_edgeCorner q hoff hy) hnonpos

end

end RHTower
