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
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 16).re := by
  refine GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos
    (t := 981 / 10000) hA ?_ ?_
  · have hsq : (10000 * B) ^ 2 < (981 * A) ^ 2 := by nlinarith [sq_pos_of_pos hA]
    have habsScaled : |10000 * B| < 981 * A :=
      abs_lt_of_sq_lt_sq hsq (mul_nonneg (by norm_num) hA.le)
    rw [abs_mul] at habsScaled
    norm_num at habsScaled
    nlinarith
  · norm_num
    nlinarith [Real.pi_gt_d20]

/-- Off the critical line, the central four-fifths of the critical strip satisfies the rational
order-sixteen sector certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSixteenSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 5 : ℝ))
    {y : ℝ} (hy : 1 / 4 < y) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hu : u ≤ 1 / 5 := by simpa only [u] using hinner
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 104 * B ^ 2 ≤ (416 / 5 : ℝ) * v := by
    rw [hB]
    nlinarith
  have hheight : (416 / 5 : ℝ) * v < v ^ 2 := by
    nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 104 * B ^ 2 < A ^ 2
  linarith

/-- Every Xi zero above squared height `104` satisfies the rational order-sixteen sector
certificate at every absolute-Euler squared coordinate. -/
theorem xiOrderSixteenSectorRatio_of_oneHundredFour_le_im_sq
    (q : XiZeroCopy) (hhigh : 104 ≤ (q.1 : ℂ).im ^ 2)
    {y : ℝ} (hy : 1 / 4 < y) :
    104 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y) ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let A : ℝ := v - u + y
  let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : u < 1 / 4 := by
    dsimp only [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 104 ≤ v := by simpa only [v] using hhigh
  have hv0 : 0 < v := by linarith
  have hA : v < A := by
    dsimp only [A]
    nlinarith
  have hB : B ^ 2 = 4 * u * v := by
    dsimp only [B, u, v]
    ring
  have hBbound : 104 * B ^ 2 < 104 * v := by
    rw [hB]
    nlinarith
  have hheight : 104 * v ≤ v ^ 2 := by nlinarith
  have hAsq : v ^ 2 < A ^ 2 := by nlinarith
  change 104 * B ^ 2 < A ^ 2
  linarith

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
      (q.1 : ℂ).im ^ 2 < 104 := by
  have hedge : (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    by_contra h
    have hsector := xiOrderSixteenSectorRatio_of_offLine_inner q hoff
      (le_of_not_gt h) hy
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 4 : ℝ) := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hvlow : 85 < (q.1 : ℂ).im ^ 2 :=
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hvhigh : (q.1 : ℂ).im ^ 2 < 104 := by
    by_contra h
    have hsector := xiOrderSixteenSectorRatio_of_oneHundredFour_le_im_sq q
      (le_of_not_gt h) hy
    linarith
  exact ⟨hedge, hu, hvlow, hvhigh⟩

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
      (q.1 : ℂ).im ^ 2 < 104 := by
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
  have hfail : A ^ 2 ≤ 104 * B ^ 2 := by
    by_contra h
    have hsector : 104 * B ^ 2 < A ^ 2 := lt_of_not_ge h
    have hpos := orderSixteenReciprocalPower_re_pos_of_sectorRatio hA hsector
    change ((((A : ℂ) - B * I)⁻¹) ^ 16).re ≤ 0 at hnonpos
    linarith
  apply xiOrderSixteenSectorFailure_mem_edgeCorner q hoff hy
  simpa only [A, B, u, v] using hfail

end

end RHTower
