import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomSlope
import Mathlib.Analysis.Complex.Liouville

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

/-- Cauchy's estimate upgrades the uniform value decay to uniform derivative decay.  The
radius-`1/2` circle about a point on the depth-one vertical edge stays in the depth-`3/2`
strip, while its real coordinate stays at least `|R|/2` from zero once `|R| >= 2`. -/
theorem norm_deriv_xiRectangularTwoEdgeTransform_sq_vertical_le
    (L a R y : ℝ) (hR : 2 ≤ |R|) (hy : |y| ≤ 1) :
    ‖deriv (fun z : ℂ => xiRectangularTwoEdgeTransform L a z ^ 2)
        ((R : ℂ) + y * I)‖ ≤
      8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2 := by
  let z : ℂ := (R : ℂ) + y * I
  let g : ℂ → ℂ := fun w => xiRectangularTwoEdgeTransform L a w ^ 2
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hgdiff : Differentiable ℂ g := by
    intro w
    simpa only [differentiableWithinAt_univ] using
      (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a).differentiableOn
        w (Set.mem_univ w)
  have hdiff : DiffContOnCl ℂ g (Metric.ball z (1 / 2)) := by
    refine ⟨hgdiff.differentiableOn, ?_⟩
    exact hgdiff.continuous.continuousOn
  have hsphere : ∀ w ∈ Metric.sphere z (1 / 2),
      ‖g w‖ ≤
        4 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2 := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hwim : |w.im| ≤ (3 / 2 : ℝ) := by
      have himdiff : |w.im - z.im| ≤ ‖w - z‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm (w - z)
      have hzim : z.im = y := by simp [z]
      rw [hw, hzim] at himdiff
      calc
        |w.im| = |(w.im - y) + y| := by rw [sub_add_cancel]
        _ ≤ |w.im - y| + |y| := abs_add_le _ _
        _ ≤ 1 / 2 + 1 := add_le_add himdiff hy
        _ = 3 / 2 := by ring
    have hwre : |(I * w).re| ≤ (3 / 2 : ℝ) := by
      simpa [Complex.mul_re, Complex.mul_im] using hwim
    have hwR : |R| / 2 ≤ ‖I * w‖ := by
      have hRw : |R| - 1 / 2 ≤ ‖w‖ := by
        have hrev := norm_sub_norm_le z w
        have hznorm : |R| ≤ ‖z‖ := by
          have := Complex.abs_re_le_norm z
          simpa [z] using this
        rw [norm_sub_rev, hw] at hrev
        linarith
      rw [norm_mul, norm_I, one_mul]
      linarith
    have hw0 : I * w ≠ 0 := by
      intro hzero
      have : ‖I * w‖ = 0 := by rw [hzero, norm_zero]
      rw [this] at hwR
      have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
      linarith
    have hvalue := norm_rectangularTwoEdgeTransform_le_on_strip
      L a hw0 hwre
    change ‖xiRectangularTwoEdgeTransform L a w ^ 2‖ ≤ _
    rw [norm_pow, xiRectangularTwoEdgeTransform]
    have hdiv : rectangularTransformStripBound L a (3 / 2) / ‖I * w‖ ≤
        2 * rectangularTransformStripBound L a (3 / 2) / |R| := by
      have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
      calc
        rectangularTransformStripBound L a (3 / 2) / ‖I * w‖ ≤
            rectangularTransformStripBound L a (3 / 2) / (|R| / 2) :=
          div_le_div_of_nonneg_left
            (rectangularTransformStripBound_nonneg L a (3 / 2))
            (by positivity) hwR
        _ = 2 * rectangularTransformStripBound L a (3 / 2) / |R| := by
          field_simp
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) (hvalue.trans hdiv) 2
    calc
      ‖rectangularTwoEdgeTransform L a (I * w)‖ ^ 2 ≤
          (2 * rectangularTransformStripBound L a (3 / 2) / |R|) ^ 2 := hsquare
      _ = 4 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2 := by
        rw [div_pow, sq_abs]
        ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hhalf hdiff hsphere
  change ‖deriv g z‖ ≤ _
  calc
    ‖deriv g z‖ ≤
        (4 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2) /
          (1 / 2) := hcauchy
    _ = 8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2 := by ring

end RHTower
