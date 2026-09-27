import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalSlope

/-!
# Monotonicity in the full Gaussian strip radius

Shrinking the nonnegative strip radius decreases every complete defect and
slope. This permits one degree-normalized envelope to control smaller scales.
-/

open scoped Real NNReal
noncomputable section

namespace GaloisForLFunctions

theorem verticalPolynomialGaussianDefect_radius_mono (d : ℕ) :
    Monotone (fun R : ℝ≥0 => verticalPolynomialGaussianDefect d R) := by
  intro R S hRS
  change verticalPolynomialGaussianDefect d R ≤ verticalPolynomialGaussianDefect d S
  have hrs : (R : ℝ) ≤ (S : ℝ) := hRS
  have hg := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ R.coe_nonneg hrs 2) Real.pi_pos.le)
  have hp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrs (Real.sqrt_nonneg (4 * π * d)))
  have hx := mul_le_mul_of_nonneg_right hrs (Real.sqrt_nonneg (4 * π * ((d : ℝ) + 1)))
  have hb : 0 ≤ Real.exp ((R : ℝ) * Real.sqrt (4 * π * d)) - 1 +
      (R : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 1)) :=
    add_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (by positivity)
  unfold verticalPolynomialGaussianDefect
  rw [abs_of_nonneg R.coe_nonneg, abs_of_nonneg S.coe_nonneg]
  exact add_le_add (mul_le_mul hg (add_le_add (sub_le_sub_right hp 1) hx)
    hb (Real.exp_pos _).le) (sub_le_sub_right hg 1)

theorem gaussianVerticalDefectSlope_radius_mono (d : ℕ) :
    Monotone (fun R : ℝ≥0 => gaussianVerticalDefectSlope d R) := by
  intro R S hRS
  have hrs : (R : ℝ) ≤ (S : ℝ) := hRS
  have hg := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ R.coe_nonneg hrs 2) Real.pi_pos.le)
  have hp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrs (Real.sqrt_nonneg (4 * π * d)))
  unfold gaussianVerticalDefectSlope
  exact mul_le_mul hg (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)) le_rfl)
    (mul_le_mul_of_nonneg_left hrs Real.pi_pos.le)) (by positivity) (Real.exp_pos _).le

theorem gaussianCoordinateVerticalSlope_radius_mono (d : ℕ) :
    Monotone (fun R : ℝ≥0 => gaussianCoordinateVerticalSlope d R) := by
  intro R S hRS
  unfold gaussianCoordinateVerticalSlope
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (gaussianVerticalDefectSlope_radius_mono (d + 1) hRS)
        (gaussianStripSamplingFactor_nonneg _ _)) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (add_le_add (verticalPolynomialGaussianDefect_radius_mono d hRS) le_rfl)
      (gaussianStripSamplingFactor_nonneg _ _)

end GaloisForLFunctions
