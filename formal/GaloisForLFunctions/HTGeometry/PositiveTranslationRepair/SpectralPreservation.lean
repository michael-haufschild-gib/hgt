import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.PositiveLaplaceRepair
import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.PolynomialTransforms

/-! Positive translation repair preserves any prescribed nonzero complex Laplace
value when the mesh is sufficiently small. All absolute exponential moments
survive the finite translation average. -/

open MeasureTheory Polynomial
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

theorem integrable_cexp_of_abs_moment {f : ℝ → ℝ} (hf : Continuous f) (w : ℂ)
    (hm : Integrable fun x => Real.exp (|w.re| * |x|) * |f x|) :
    Integrable fun x : ℝ => (f x : ℂ) * Complex.exp (w * x) := by
  apply hm.mono' (show Continuous (fun x : ℝ => (f x : ℂ) * Complex.exp (w * x)) by fun_prop).aestronglyMeasurable
  filter_upwards [] with x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using
    abs_mul_exp_le (s := w.re) (le_refl |w.re|) f x


/-- Finite translation averages retain all absolute exponential moments. -/
theorem polynomialAverage_abs_moment (p : ℝ[X]) (h : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f)
    (hm : ∀ c : ℝ, Integrable fun x => Real.exp (c * |x|) * |f x|) (c : ℝ) :
    Integrable fun x => Real.exp (c * |x|) * |polynomialAverage p h f x| := by
  have hi (s : ℝ) := integrable_polynomialAverage_exp p h s
    (integrable_mul_exp_of_abs_moment hf.measurable (le_refl |s|) (hm |s|))
  apply ((hi c).abs.add (hi (-c)).abs).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (continuous_polynomialAverage p h hf).abs).aestronglyMeasurable
  filter_upwards [] with x
  change abs (Real.exp (c * |x|) * |polynomialAverage p h f x|) ≤
    |polynomialAverage p h f x * Real.exp (c * x)| +
      |polynomialAverage p h f x * Real.exp (-c * x)|
  simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith only [mul_nonneg (abs_nonneg (polynomialAverage p h f x)) (Real.exp_pos (-c * x)).le]
  · rw [abs_of_nonpos (lt_of_not_ge hx).le, mul_neg, ← neg_mul]
    nlinarith only [mul_nonneg (abs_nonneg (polynomialAverage p h f x)) (Real.exp_pos (c * x)).le]

/-- Positive translation repair can preserve any chosen nonzero complex Laplace value. -/
theorem exists_positive_average_preserving_character {f : ℝ → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 < L) (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hmoment : ∀ c : ℝ, Integrable fun x => Real.exp (c * |x|) * |f x|)
    (htail : ∃ A : ℝ, ∀ x, A < |x| → 0 < f x)
    (hlap : ∀ s : ℝ, 0 < ∫ x, f x * Real.exp (s * x))
    (w : ℂ) (hw : (∫ x : ℝ, (f x : ℂ) * Complex.exp (w * x)) ≠ 0) :
    ∃ (h : ℝ) (r : List ℝ), 0 < h ∧ (∀ a ∈ r, 0 < a) ∧
      (∀ x, 0 ≤ polynomialAverage (negativeRootMultiplier r) h f x) ∧
      (∫ x : ℝ, (polynomialAverage (negativeRootMultiplier r) h f x : ℂ) *
        Complex.exp (w * x)) ≠ 0 := by
  have hδ : 0 < Real.pi / (2 * (|w.im| + 1)) := by positivity
  obtain ⟨h, r, hh, hhδ, hr, hpos⟩ :=
    exists_positive_average_of_laplace_positive hf hL hlip hmoment htail hlap hδ
  refine ⟨h, r, hh, hr, hpos, ?_⟩
  rw [integral_polynomialAverage_cexp _ _ _ (integrable_cexp_of_abs_moment hf w (hmoment _))]
  apply mul_ne_zero _ hw
  apply negativeRootMultiplier_eval₂_exp_ne_zero hr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    abs_mul, abs_of_pos hh]
  have hb := (lt_div_iff₀ (by positivity : 0 < 2 * (|w.im| + 1))).mp hhδ
  nlinarith only [hb, hh]

#print axioms polynomialAverage_abs_moment
#print axioms exists_positive_average_preserving_character
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
