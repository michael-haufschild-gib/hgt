import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalError

/-!
# Explicit linear slopes for the complete Gaussian strip defect

The full exponential defect admits a linear-radius upper bound. The coefficient
is continuous at radius zero, so the reciprocal-square summation loss can be
cancelled without differentiating a norm or discarding cross terms.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- A continuous degree-dependent slope for the complete vertical defect. -/
def gaussianVerticalDefectSlope (d : ℕ) (R : ℝ) : ℝ :=
  Real.exp (π * R ^ 2) *
    (Real.sqrt (4 * π * d) * Real.exp (R * Real.sqrt (4 * π * d)) +
      Real.sqrt (4 * π * ((d : ℝ) + 1)) + π * R)

theorem gaussianVerticalDefectSlope_nonneg (d : ℕ) (R : ℝ≥0) :
    0 ≤ gaussianVerticalDefectSlope d R := by
  unfold gaussianVerticalDefectSlope
  positivity

theorem gaussianVerticalDefectSlope_mono (R : ℝ≥0) :
    Monotone (fun d : ℕ => gaussianVerticalDefectSlope d R) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  have hA := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hc
    (by positivity : (0 : ℝ) ≤ 4 * π))
  have hA' := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add hc (le_refl 1))
    (by positivity : (0 : ℝ) ≤ 4 * π))
  unfold gaussianVerticalDefectSlope
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply add_le_add _ le_rfl
  apply add_le_add _ hA'
  exact mul_le_mul hA (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA R.coe_nonneg))
    (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- The full defect is at most radius times its explicit slope. -/
theorem verticalPolynomialGaussianDefect_le_radius_mul_slope (d : ℕ) (R : ℝ≥0) :
    verticalPolynomialGaussianDefect d R ≤ (R : ℝ) * gaussianVerticalDefectSlope d R := by
  have hexp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x) (Real.exp_pos x).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    linarith only [h]
  have hp := mul_le_mul_of_nonneg_left (hexp ((R : ℝ) * Real.sqrt (4 * π * d)))
    (Real.exp_pos (π * (R : ℝ) ^ 2)).le
  have hg := hexp (π * (R : ℝ) ^ 2)
  unfold verticalPolynomialGaussianDefect gaussianVerticalDefectSlope
  rw [abs_of_nonneg R.coe_nonneg]
  nlinarith only [hp, hg]

/-- The slope of the coordinate-weighted defect, in the same whole-polynomial norm. -/
def gaussianCoordinateVerticalSlope (d : ℕ) (R : ℝ) : ℝ :=
  gaussianStripSamplingFactor (d + 1) 1 * gaussianVerticalDefectSlope (d + 1) R *
      (Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π)) +
    gaussianStripSamplingFactor d 1 * (verticalPolynomialGaussianDefect d R + 1)

theorem gaussianCoordinateVerticalSlope_nonneg (d : ℕ) (R : ℝ≥0) :
    0 ≤ gaussianCoordinateVerticalSlope d R := by
  unfold gaussianCoordinateVerticalSlope gaussianVerticalDefectSlope
  have hC := gaussianStripSamplingFactor_nonneg (d + 1) 1
  have hC' := gaussianStripSamplingFactor_nonneg d 1
  have hE := verticalPolynomialGaussianDefect_nonneg d R
  positivity

theorem gaussianCoordinateVerticalSlope_mono (R : ℝ≥0) :
    Monotone (fun d : ℕ => gaussianCoordinateVerticalSlope d R) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  have hA := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (add_le_add hc (le_refl 1))
      (by positivity : (0 : ℝ) ≤ 4 * π))) (by positivity : (0 : ℝ) ≤ 2 * π)
  unfold gaussianCoordinateVerticalSlope
  apply add_le_add
  · exact mul_le_mul (mul_le_mul (gaussianStripSamplingFactor_mono 1 (Nat.add_le_add_right hde 1))
      (gaussianVerticalDefectSlope_mono R (Nat.add_le_add_right hde 1))
      (gaussianVerticalDefectSlope_nonneg _ _) (gaussianStripSamplingFactor_nonneg _ _)) hA
      (by positivity) (mul_nonneg (gaussianStripSamplingFactor_nonneg _ _)
        (gaussianVerticalDefectSlope_nonneg _ _))
  · exact mul_le_mul (gaussianStripSamplingFactor_mono 1 hde)
      (add_le_add (verticalPolynomialGaussianDefect_mono R hde) le_rfl)
      (add_nonneg (verticalPolynomialGaussianDefect_nonneg _ _) (by positivity))
      (gaussianStripSamplingFactor_nonneg _ _)

/-- Coordinate error is linear in radius with an explicit coefficient. -/
theorem gaussianCoordinateVerticalDefect_le_radius_mul_slope (d : ℕ) (R : ℝ≥0) :
    gaussianCoordinateVerticalDefect d R ≤ (R : ℝ) * gaussianCoordinateVerticalSlope d R := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (verticalPolynomialGaussianDefect_le_radius_mul_slope (d + 1) R)
      (gaussianStripSamplingFactor_nonneg (d + 1) 1))
    (by positivity : 0 ≤ Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π))
  unfold gaussianCoordinateVerticalDefect gaussianCoordinateVerticalSlope
  nlinarith only [h]

/-- There is no radius singularity in the slope coefficient. -/
theorem continuous_gaussianCoordinateVerticalSlope (d : ℕ) :
    Continuous (gaussianCoordinateVerticalSlope d) := by
  unfold gaussianCoordinateVerticalSlope gaussianVerticalDefectSlope verticalPolynomialGaussianDefect
  fun_prop

end GaloisForLFunctions
