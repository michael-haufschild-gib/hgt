import GaloisForLFunctions.RHTower.XiGaussianFixedTimeCoercivityObstruction
import GaloisForLFunctions.RHTower.XiGaussianThreeHalvesTrace
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Fixed-time failure of the fractional phase ceiling

Even after choosing its interpolation scale separately for every polynomial,
the fractional continuous-norm ceiling cannot be dominated by the actual
positive sampled energy at a fixed positive heat time. This concerns the
ceiling, not the actual phase debt or the sign of a Hankel form.
-/

open Complex MeasureTheory GaloisForLFunctions
open scoped Real SchwartzMap NNReal
noncomputable section

namespace RHTower

theorem xiHeatThreeHalvesMass_pos : 0 < xiHeatThreeHalvesMass := by
  obtain ⟨q⟩ := nonempty_xiZeroCopy
  have hq : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hle := xiSpectralPoint_inv_three_halves_summable.sum_le_tsum
    ({q} : Finset XiZeroCopy) (fun _ _ => by positivity)
  simp only [Finset.sum_singleton] at hle
  exact (show 0 < 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖) by
    positivity).trans_le hle

private theorem min_le_quadratic_div_sqrt
    (A B L : {x : ℝ // 0 < x}) :
    min (A : ℝ) B ≤ ((A : ℝ) * (L : ℝ) ^ 2 + B) / Real.sqrt (L : ℝ) := by
  have hs : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr L.property
  have hs2 := Real.sq_sqrt L.property.le
  have hk : 0 < min (A : ℝ) B := lt_min A.property B.property
  rw [le_div_iff₀ hs]
  rcases le_total (L : ℝ) 1 with hL | hL
  · have hsqrt : Real.sqrt (L : ℝ) ≤ 1 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsqrt hk.le
    nlinarith [min_le_right (A : ℝ) (B : ℝ),
      mul_nonneg A.property.le (sq_nonneg (L : ℝ))]
  · have hsone : 1 ≤ Real.sqrt (L : ℝ) := by nlinarith
    have hsL : Real.sqrt (L : ℝ) ≤ (L : ℝ) := by
      nlinarith [sq_nonneg (Real.sqrt (L : ℝ) - 1)]
    have hsqrt : Real.sqrt (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsqrt hk.le
    have hA := mul_le_mul_of_nonneg_right (min_le_left (A : ℝ) (B : ℝ))
      (sq_nonneg (L : ℝ))
    linarith [B.property]

/-- A positive floor survives every degree and every interpolation scale. -/
theorem exists_xiGaussianThreeHalvesPhaseBudget_uniform_pos
    (r : {r : ℝ // 0 < r}) :
    ∃ b : ℝ, 0 < b ∧ ∀ d : ℕ, ∀ L : {L : ℝ // 0 < L},
      b ≤ xiGaussianThreeHalvesPhaseBudget d r L := by
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  have hv : 0 < gaussianVerticalDefectSlope 0 R := by
    unfold gaussianVerticalDefectSlope
    have hR := R.coe_nonneg
    positivity
  have hg (d : ℕ) : 0 < gaussianStripSamplingFactor d 1 := by
    unfold gaussianStripSamplingFactor
    positivity
  have hc : 0 < gaussianCoordinateVerticalSlope 0 R := by
    have hE := verticalPolynomialGaussianDefect_nonneg 0 R
    have hv1 := gaussianVerticalDefectSlope_nonneg 1 R
    unfold gaussianCoordinateVerticalSlope
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (mul_nonneg (hg 1).le hv1) (by positivity)
    · exact mul_pos (hg 0) (by linarith)
  let A := (r : ℝ) ^ 2 * (gaussianStripSamplingFactor 0 1 *
    gaussianVerticalDefectSlope 0 R) ^ 2
  let B := 2 * gaussianCoordinateVerticalSlope 0 R ^ 2
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (pow_pos r.property 2) (pow_pos (mul_pos (hg 0) hv) 2)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨xiHeatThreeHalvesMass / 2 * min A B,
    mul_pos (div_pos xiHeatThreeHalvesMass_pos (by positivity)) (lt_min hA hB), ?_⟩
  intro d L
  have h := mul_le_mul_of_nonneg_left
    (min_le_quadratic_div_sqrt ⟨A, hA⟩ ⟨B, hB⟩ L)
    (div_nonneg xiHeatThreeHalvesMass_nonneg (by positivity) :
      0 ≤ xiHeatThreeHalvesMass / 2)
  have heq : xiHeatThreeHalvesMass / 2 *
      (A * (L : ℝ) ^ 2 + B) / Real.sqrt (L : ℝ) =
      xiGaussianThreeHalvesPhaseBudget 0 r L := by
    unfold xiGaussianThreeHalvesPhaseBudget
    change xiHeatThreeHalvesMass / 2 * (A * (L : ℝ) ^ 2 + B) / Real.sqrt (L : ℝ) =
      xiHeatThreeHalvesMass / (2 * Real.sqrt (L : ℝ)) *
        ((r : ℝ) ^ 2 * (L : ℝ) ^ 2 *
          (gaussianStripSamplingFactor 0 1 * gaussianVerticalDefectSlope 0 R) ^ 2 +
          2 * gaussianCoordinateVerticalSlope 0 R ^ 2)
    dsimp only [A, B]
    ring
  have hzero : xiHeatThreeHalvesMass / 2 * min A B ≤
      xiGaussianThreeHalvesPhaseBudget 0 r L := by
    rw [← heq]
    simpa only [mul_div_assoc] using h
  exact hzero.trans (xiGaussianThreeHalvesPhaseBudget_mono
    ⟨r, r.property.le⟩ ⟨L, L.property.le⟩ (Nat.zero_le d))

/-- Optimizing the fractional ceiling separately for each polynomial cannot
make the actual energy dominate it at a fixed positive scale. -/
theorem not_forall_xiGaussian_energy_dominates_fractional_budget
    (r : {r : ℝ // 0 < r}) :
    ¬ ∀ P : Polynomial ℝ, ∃ L : {L : ℝ // 0 < L},
      xiGaussianThreeHalvesPhaseBudget (2 * P.natDegree) r L *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2
          (volume : Measure ℝ)‖ ^ 2 ≤ xiScaledEvenGaussianEnergy P r := by
  intro hdom
  obtain ⟨b, hb, hbudget⟩ := exists_xiGaussianThreeHalvesPhaseBudget_uniform_pos r
  apply not_exists_xiScaledEvenGaussian_uniform_norm_floor r
  refine ⟨b, hb, fun P => ?_⟩
  obtain ⟨L, hL⟩ := hdom P
  exact (mul_le_mul_of_nonneg_right (hbudget (2 * P.natDegree) L) (sq_nonneg _)).trans hL

end RHTower
