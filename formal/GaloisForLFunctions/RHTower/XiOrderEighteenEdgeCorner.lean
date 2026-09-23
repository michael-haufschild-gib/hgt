import GaloisForLFunctions.RHTower.XiOrderSeventeenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-eighteen squared-Xi source

The order-eighteen radial atom is controlled by the nineteenth reciprocal power of
`A - B*I`, where `A = gamma^(2 : ℕ) - delta^(2 : ℕ) + y` and `B = 2*delta*gamma`.

The rational sector coefficient `147` protects `delta^(2 : ℕ) <= 7/50` and every zero above squared
height `147`. Thus, at every `y > 1/4`, failure forces an off-critical zero into

`7/50 < delta^(2 : ℕ) < 1/4`, `85 < gamma^(2 : ℕ) < 147`.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/147` has a
strictly positive nineteenth reciprocal power. -/
theorem orderNineteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 147 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (19 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 826 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

/-- The protected central band satisfies the rational order-nineteen sector certificate. -/
theorem xiOrderNineteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (7 / 50 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 147) (u₀ := 7 / 50)
    (v₀ := 85) (y₀ := 1 / 4) (by norm_num) hy.le hinner
    (xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff).le (by norm_num) (by norm_num)

/-- Every Xi zero above squared height `147` satisfies the rational order-nineteen sector
certificate. -/
theorem xiOrderNineteenSectorRatio_of_oneHundredFortySeven_le_im_sq
    (q : XiZeroCopy) (hhigh : 147 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    {y : ℝ} (hy : 1 / 4 < y) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) := by
  exact GaloisForLFunctions.HTGeometry.sector_ratio_of_corner_of_lt_width (N := 147)
    (u₀ := 1 / 4) (v₀ := 147) (y₀ := 1 / 4) (by norm_num) hy.le
    (xi_divisor_support_centered_re_sq_lt_quarter q.1) hhigh (by norm_num) (by norm_num)
    (by norm_num)

/-- Sector failure at `y > 1/4` forces the exact order-eighteen compact edge corner. -/
theorem xiOrderNineteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y) ^ (2 : ℕ) ≤
        147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 147 :=
  xiZeroCopy_sectorFailure_mem_edgeCorner q hoff
    (fun h => xiOrderNineteenSectorRatio_of_offLine_inner q hoff h hy)
    (fun h => xiOrderNineteenSectorRatio_of_oneHundredFortySeven_le_im_sq q h hy) hfail

/-- A nonpositive nineteenth reciprocal-power atom must lie in the compact edge corner. -/
theorem xiOrderNineteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ (19 : ℕ)).re ≤ 0) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 147 :=
  xiZeroCopy_reciprocalPower_nonpos_of_sector q hy
    (fun _ _ hA h => orderNineteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiOrderNineteenSectorFailure_mem_edgeCorner q hoff hy) hnonpos

end

end RHTower
