import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomSlope

/-!
# Uniform vertical decay of the sharp rectangular Xi test

The existing divisor-side estimate only needs the half-width critical strip.  A symmetric
Guinand--Weil rectangle uses the larger fixed strip `|Im z| <= 1`, equivalently
`|(I*z).re| <= 1` in the bilateral-transform coordinate.  This module proves the corresponding
uniform bound with an arbitrary nonnegative strip width and specializes it to the vertical edge.

The result is the analytic decay input for eliminating the vertical contour edge: the sharp
rectangular transform is `O(1/R)` and its square is `O(1/R^2)`, uniformly along the whole edge.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- Exponential numerator constant for the two-edge transform on `|Re w| <= c`. -/
def rectangularTransformStripBound (L a c : ℝ) : ℝ :=
  (1 + Real.exp (|L| * c)) *
    (Real.exp (|a| * c) + Real.exp (|a - L| * c))

theorem rectangularTransformStripBound_nonneg (L a c : ℝ) :
    0 ≤ rectangularTransformStripBound L a c := by
  unfold rectangularTransformStripBound
  positivity

private theorem real_mul_re_le_abs_mul
    {b c : ℝ} {w : ℂ} (hw : |w.re| ≤ b) :
    ((c : ℂ) * w).re ≤ |c| * b := by
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    c * w.re ≤ |c * w.re| := le_abs_self _
    _ = |c| * |w.re| := abs_mul c w.re
    _ ≤ |c| * b := mul_le_mul_of_nonneg_left hw (abs_nonneg c)

/-- A rectangular-window amplitude is uniformly reciprocal-linear on every fixed vertical
strip. -/
theorem norm_rectangularWindowAmplitude_le_on_strip
    (L : ℝ) {c : ℝ} {w : ℂ} (hw : w ≠ 0)
    (hwre : |w.re| ≤ c) :
    ‖rectangularWindowAmplitude L w‖ ≤
      (1 + Real.exp (|L| * c)) / ‖w‖ := by
  rw [rectangularWindowAmplitude_eq_div hw, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg w)
  calc
    ‖1 - Complex.exp (-(L : ℂ) * w)‖ ≤
        ‖(1 : ℂ)‖ + ‖Complex.exp (-(L : ℂ) * w)‖ := norm_sub_le _ _
    _ = 1 + Real.exp ((-(L : ℂ) * w).re) := by
      rw [norm_one, Complex.norm_exp]
    _ ≤ 1 + Real.exp (|L| * c) := by
      gcongr
      simpa only [ofReal_neg, neg_mul, abs_neg] using
        (real_mul_re_le_abs_mul (c := -L) hwre)

/-- The complete two-edge transform is uniformly `O(1/‖w‖)` on every fixed vertical strip. -/
theorem norm_rectangularTwoEdgeTransform_le_on_strip
    (L a : ℝ) {c : ℝ} {w : ℂ} (hw : w ≠ 0)
    (hwre : |w.re| ≤ c) :
    ‖rectangularTwoEdgeTransform L a w‖ ≤
      rectangularTransformStripBound L a c / ‖w‖ := by
  rw [rectangularTwoEdgeTransform_eq hw, norm_mul]
  calc
    ‖rectangularWindowAmplitude L w‖ *
        ‖Complex.exp ((a : ℂ) * w) + Complex.exp (-(a - L : ℂ) * w)‖ ≤
      ((1 + Real.exp (|L| * c)) / ‖w‖) *
        (‖Complex.exp ((a : ℂ) * w)‖ +
          ‖Complex.exp (-(a - L : ℂ) * w)‖) := by
      gcongr
      · exact norm_rectangularWindowAmplitude_le_on_strip L hw hwre
      · exact norm_add_le _ _
    _ ≤ ((1 + Real.exp (|L| * c)) / ‖w‖) *
        (Real.exp (|a| * c) + Real.exp (|a - L| * c)) := by
      gcongr
      · rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (real_mul_re_le_abs_mul hwre)
      · rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (by
          simpa only [ofReal_neg, ofReal_sub, neg_mul, abs_neg] using
            (real_mul_re_le_abs_mul (c := -(a - L)) hwre))
    _ = rectangularTransformStripBound L a c / ‖w‖ := by
      unfold rectangularTransformStripBound
      field_simp

/-- Uniform reciprocal-linear decay on the right vertical side of the symmetric depth-one
rectangle. -/
theorem norm_xiRectangularTwoEdgeTransform_vertical_le
    (L a R y : ℝ) (hR : 0 < |R|) (hy : |y| ≤ 1) :
    ‖xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I)‖ ≤
      rectangularTransformStripBound L a 1 / |R| := by
  let z : ℂ := (R : ℂ) + y * I
  let w : ℂ := I * z
  have hwre : |w.re| ≤ (1 : ℝ) := by
    dsimp only [w, z]
    simpa [Complex.mul_re, Complex.mul_im] using hy
  have hwim : w.im = R := by
    dsimp only [w, z]
    simp [Complex.mul_re, Complex.mul_im]
  have hw : w ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [hwim] at him
    simp at him
    exact (ne_of_gt hR) (abs_eq_zero.mpr him)
  have hraw := norm_rectangularTwoEdgeTransform_le_on_strip
    L a (c := (1 : ℝ)) hw hwre
  have hRnorm : |R| ≤ ‖w‖ := by
    rw [← hwim]
    exact Complex.abs_im_le_norm w
  rw [xiRectangularTwoEdgeTransform]
  exact hraw.trans (div_le_div_of_nonneg_left
    (rectangularTransformStripBound_nonneg L a 1) hR hRnorm)

/-- The squared sharp Xi test has uniform `R^-2` decay along the complete vertical edge. -/
theorem norm_xiRectangularTwoEdgeTransform_vertical_sq_le
    (L a R y : ℝ) (hR : 0 < |R|) (hy : |y| ≤ 1) :
    ‖xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ 2‖ ≤
      rectangularTransformStripBound L a 1 ^ 2 / R ^ 2 := by
  rw [norm_pow]
  have h := norm_xiRectangularTwoEdgeTransform_vertical_le L a R y hR hy
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    ‖xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I)‖ ^ 2 ≤
        (rectangularTransformStripBound L a 1 / |R|) ^ 2 := hsquare
    _ = rectangularTransformStripBound L a 1 ^ 2 / R ^ 2 := by
      rw [div_pow, sq_abs]

end RHTower
