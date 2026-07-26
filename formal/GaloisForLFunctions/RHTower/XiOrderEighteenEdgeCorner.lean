import GaloisForLFunctions.RHTower.XiOrderSeventeenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-eighteen squared-Xi source

The order-eighteen radial atom is controlled by the nineteenth reciprocal power of
`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

The rational sector coefficient `147` protects `delta^2 <= 7/50` and every zero above squared
height `147`. Thus, at every `y > 1/4`, failure forces an off-critical zero into

`7/50 < delta^2 < 1/4`, `85 < gamma^2 < 147`.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/147` has a
strictly positive nineteenth reciprocal power. -/
theorem orderNineteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 147 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 19).re := by
  refine GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos
    (t := 826 / 10000) hA ?_ ?_
  · have hsq : (10000 * B) ^ 2 < (826 * A) ^ 2 := by nlinarith [sq_pos_of_pos hA]
    have habsScaled : |10000 * B| < 826 * A :=
      abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  · norm_num
    nlinarith [Real.pi_gt_d20]

/-- The protected central band satisfies the rational order-nineteen sector certificate. -/
theorem xiOrderNineteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (7 / 50 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 7 / 50 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 147 * B ^ 2 ≤ (2058 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (2058 / 25 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 147 * B ^ 2 < A ^ 2
  linarith

/-- Every Xi zero above squared height `147` satisfies the rational order-nineteen sector
certificate. -/
theorem xiOrderNineteenSectorRatio_of_oneHundredFortySeven_le_im_sq
    (q : XiZeroCopy) (hhigh : 147 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 147 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 147 * B ^ 2 < 147 * v := by
    rw [hB]
    nlinarith
  have hheight : 147 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 147 * B ^ 2 < A ^ 2
  linarith

/-- Sector failure at `y > 1/4` forces the exact order-eighteen compact edge corner. -/
theorem xiOrderNineteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        147 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 147 := by
  have hedge : (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderNineteenSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 147 := by
    by_contra h
    have hsector := xiOrderNineteenSectorRatio_of_oneHundredFortySeven_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- A nonpositive nineteenth reciprocal-power atom must lie in the compact edge corner. -/
theorem xiOrderNineteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 19).re ≤ 0) :
    (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 147 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith
  have hfail : A ^ 2 ≤ 147 * B ^ 2 := by
    by_contra h
    have hsector : 147 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderNineteenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 19).re ≤ 0 at hnonpos
    linarith
  apply xiOrderNineteenSectorFailure_mem_edgeCorner q hoff hy
  simpa only [A, B, u, v] using hfail

end

end RHTower
