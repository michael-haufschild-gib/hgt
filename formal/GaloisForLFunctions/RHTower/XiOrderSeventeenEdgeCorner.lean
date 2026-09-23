import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-seventeen squared-Xi source

The order-seventeen radial atom is controlled by the eighteenth reciprocal power of
`A - B*I`, where `A = gamma^(2 : ℕ) - delta^(2 : ℕ) + y` and `B = 2*delta*gamma`.

The rational sector coefficient `132` protects `delta^(2 : ℕ) <= 4/25` and every zero above squared
height `132`. Thus, at every `y > 1/4`, failure forces an off-critical zero into

`4/25 < delta^(2 : ℕ) < 1/4`, `85 < gamma^(2 : ℕ) < 132`.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/132` has a
strictly positive eighteenth reciprocal power. -/
theorem orderEighteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 132 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (18 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 872 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

/-- The protected central band satisfies the rational order-eighteen sector certificate. -/
theorem xiOrderEighteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (4 / 25 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 132) (u₀ := 4 / 25)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Every Xi zero above squared height `132` satisfies the rational order-eighteen sector
certificate. -/
theorem xiOrderEighteenSectorRatio_of_oneHundredThirtyTwo_le_im_sq
    (q : XiZeroCopy) (hhigh : 132 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    {y : ℝ} (hy : 1 / 4 < y) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 132)
    (u₀ := 1 / 4) (v₀ := 132) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

/-- Sector failure at `y > 1/4` forces the exact order-seventeen compact edge corner. -/
theorem xiOrderEighteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) ≤
        132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 132 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderEighteenSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderEighteenSectorRatio_of_oneHundredThirtyTwo_le_im_sq q h hy) hfail

/-- A nonpositive eighteenth reciprocal-power atom must lie in the compact edge corner. -/
theorem xiOrderEighteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ (18 : ℕ)).re ≤ 0) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 132 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderEighteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiOrderEighteenSectorFailure_mem_edgeCorner q hoff hy) hnonpos

end

end RHTower
