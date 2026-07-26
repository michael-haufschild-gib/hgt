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
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 17).re := by
  refine GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos
    (t := 923 / 10000) hA ?_ ?_
  · have hsq : (10000 * B) ^ 2 < (923 * A) ^ 2 := by nlinarith [sq_pos_of_pos hA]
    have habsScaled : |10000 * B| < 923 * A :=
      abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  · norm_num
    nlinarith [Real.pi_gt_d20]

/-- Off the critical line, the protected central band satisfies the rational order-seventeen
sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (9 / 50 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 9 / 50 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 118 * B ^ 2 ≤ (2124 / 25 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (2124 / 25 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 118 * B ^ 2 < A ^ 2
  linarith

/-- Every Xi zero above squared height `118` satisfies the rational order-seventeen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq
    (q : XiZeroCopy) (hhigh : 118 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    118 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 118 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 118 * B ^ 2 < 118 * v := by
    rw [hB]
    nlinarith
  have hheight : 118 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 118 * B ^ 2 < A ^ 2
  linarith

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
      (q.1 : ℂ).im ^ 2 < 118 := by
  have hedge : (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderSeventeenSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 118 := by
    by_contra h
    have hsector := xiOrderSeventeenSectorRatio_of_oneHundredEighteen_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

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
      (q.1 : ℂ).im ^ 2 < 118 := by
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
  have hfail : A ^ 2 ≤ 118 * B ^ 2 := by
    by_contra h
    have hsector : 118 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 17).re ≤ 0 at hnonpos
    linarith
  apply xiOrderSeventeenSectorFailure_mem_edgeCorner q hoff hy
  simpa only [A, B, u, v] using hfail

end

end RHTower
