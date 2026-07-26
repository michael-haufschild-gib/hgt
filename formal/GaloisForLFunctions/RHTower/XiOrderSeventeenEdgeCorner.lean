import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# The compact edge corner for the order-seventeen squared-Xi source

The order-seventeen radial atom is controlled by the eighteenth reciprocal power of
`A - B*I`, where `A = gamma^2 - delta^2 + y` and `B = 2*delta*gamma`.

The rational sector coefficient `132` protects `delta^2 <= 4/25` and every zero above squared
height `132`. Thus, at every `y > 1/4`, failure forces an off-critical zero into

`4/25 < delta^2 < 1/4`, `85 < gamma^2 < 132`.
-/

open Complex

namespace RHTower

noncomputable section

/-- A positive real base whose squared transverse-to-longitudinal ratio is below `1/132` has a
strictly positive eighteenth reciprocal power. -/
theorem orderEighteenReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 132 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 18).re := by
  refine GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos
    (t := 872 / 10000) hA ?_ ?_
  · have hsq : (10000 * B) ^ 2 < (872 * A) ^ 2 := by nlinarith [sq_pos_of_pos hA]
    have habsScaled : |10000 * B| < 872 * A :=
      abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  · norm_num
    nlinarith [Real.pi_gt_d20]

/-- The protected central band satisfies the rational order-eighteen sector certificate. -/
theorem xiOrderEighteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (4 / 25 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 4 / 25 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 132 * B ^ 2 ≤ (2112 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (2112 / 25 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 132 * B ^ 2 < A ^ 2
  linarith

/-- Every Xi zero above squared height `132` satisfies the rational order-eighteen sector
certificate. -/
theorem xiOrderEighteenSectorRatio_of_oneHundredThirtyTwo_le_im_sq
    (q : XiZeroCopy) (hhigh : 132 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 132 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 132 * B ^ 2 < 132 * v := by
    rw [hB]
    nlinarith
  have hheight : 132 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 132 * B ^ 2 < A ^ 2
  linarith

/-- Sector failure at `y > 1/4` forces the exact order-seventeen compact edge corner. -/
theorem xiOrderEighteenSectorFailure_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 ≤
        132 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 132 := by
  have hedge : (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderEighteenSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 132 := by
    by_contra h
    have hsector := xiOrderEighteenSectorRatio_of_oneHundredThirtyTwo_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

/-- A nonpositive eighteenth reciprocal-power atom must lie in the compact edge corner. -/
theorem xiOrderEighteenReciprocalPower_nonpos_mem_edgeCorner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {y : ℝ} (hy : 1 / 4 < y)
    (hnonpos :
      let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
      let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
      ((((A : ℂ) - B * I)⁻¹) ^ 18).re ≤ 0) :
    (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 132 := by
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
  have hfail : A ^ 2 ≤ 132 * B ^ 2 := by
    by_contra h
    have hsector : 132 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderEighteenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 18).re ≤ 0 at hnonpos
    linarith
  apply xiOrderEighteenSectorFailure_mem_edgeCorner q hoff hy
  simpa only [A, B, u, v] using hfail

end

end RHTower
