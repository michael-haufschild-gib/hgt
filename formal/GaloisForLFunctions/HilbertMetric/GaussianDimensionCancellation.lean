import GaloisForLFunctions.RHTower.TiltedHeatSaddleGaussian
import Mathlib.MeasureTheory.Integral.Prod

/-!+# Gaussian cancellation and dimension

The quadratic correction `a x² + b y² - 1` has zero Gaussian mean in two
dimensions. Its Fourier transform is exactly a negative quadratic symbol
times the Gaussian transform. On the diagonal, the same correction has
strictly negative mean instead. This is the dimension-sensitive cancellation
in Du, Lemma 7.15, applied to the existing Gaussian moment calculus.
Widths are exponentials, so integrability needs no extra premise.
-/

noncomputable section
open MeasureTheory RHTower

namespace HilbertMetric

/-- The second Fourier moment at every frequency, with positive width built in. -/
theorem gaussian_exp_second_moment (s ξ : ℝ) :
    gaussMoment (Real.exp s) 2 ξ =
      (((1 / (2 * Real.exp s) - ξ ^ 2 / (4 * Real.exp s ^ 2) : ℝ)) : ℂ) *
        gaussMoment (Real.exp s) 0 ξ := by
  rw [gaussMoment_eq (Real.exp_pos s), gaussMoment_eq (Real.exp_pos s),
    gaussJetPoly_two, gaussJetPoly_zero]
  simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    pow_zero, one_mul, pow_two, Complex.I_mul_I]
  have hs : (Real.exp s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s)
  push_cast
  field_simp
  ring

/-- Quadratic correction of the product Gaussian, including its Fourier phase. -/
def gaussianPlaneDefect (s t ξ η : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((Real.exp s : ℂ) * (p.1 : ℂ) ^ 2 + (Real.exp t : ℂ) * (p.2 : ℂ) ^ 2 - 1) *
    gaussPhase (Real.exp s) ξ p.1 * gaussPhase (Real.exp t) η p.2

private theorem gaussianPlaneDefect_split (s t ξ η : ℝ) :
    gaussianPlaneDefect s t ξ η = fun p : ℝ × ℝ =>
      (Real.exp s : ℂ) * (((p.1 : ℂ) ^ 2 * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ 0 * gaussPhase (Real.exp t) η p.2)) +
      (Real.exp t : ℂ) * (((p.1 : ℂ) ^ 0 * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ 2 * gaussPhase (Real.exp t) η p.2)) -
      (((p.1 : ℂ) ^ 0 * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ 0 * gaussPhase (Real.exp t) η p.2)) := by
  funext p
  simp only [gaussianPlaneDefect, pow_zero, one_mul]
  ring

/-- The cancellation is an equality of integrable functions, not a default integral value. -/
theorem gaussianPlaneDefect_integrable (s t ξ η : ℝ) :
    Integrable (gaussianPlaneDefect s t ξ η) := by
  rw [gaussianPlaneDefect_split]
  have h (n m : ℕ) :=
    (integrable_gaussMomentIntegrand (Real.exp_pos s) n ξ).mul_prod
      (integrable_gaussMomentIntegrand (Real.exp_pos t) m η)
  exact ((h 2 0).const_mul _ |>.add ((h 0 2).const_mul _)).sub (h 0 0)

/-- Exact Fourier symbol of the two-dimensional quadratic cancellation. -/
theorem gaussianPlaneDefect_integral (s t ξ η : ℝ) :
    (∫ p : ℝ × ℝ, gaussianPlaneDefect s t ξ η p) =
      -(((ξ ^ 2 / (4 * Real.exp s) + η ^ 2 / (4 * Real.exp t) : ℝ)) : ℂ) *
        gaussMoment (Real.exp s) 0 ξ * gaussMoment (Real.exp t) 0 η := by
  change (∫ p : ℝ × ℝ, gaussianPlaneDefect s t ξ η p
    ∂(volume : Measure ℝ).prod volume) = _
  rw [gaussianPlaneDefect_split]
  have h (n m : ℕ) :=
    (integrable_gaussMomentIntegrand (Real.exp_pos s) n ξ).mul_prod
      (integrable_gaussMomentIntegrand (Real.exp_pos t) m η)
  have hsum : Integrable (fun p : ℝ × ℝ =>
      (Real.exp s : ℂ) * (((p.1 : ℂ) ^ 2 * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ 0 * gaussPhase (Real.exp t) η p.2)) +
      (Real.exp t : ℂ) * (((p.1 : ℂ) ^ 0 * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ 2 * gaussPhase (Real.exp t) η p.2)))
      ((volume : Measure ℝ).prod volume) :=
    ((h 2 0).const_mul (Real.exp s : ℂ)).add ((h 0 2).const_mul (Real.exp t : ℂ))
  have hsep (n m : ℕ) :
      (∫ p : ℝ × ℝ, ((p.1 : ℂ) ^ n * gaussPhase (Real.exp s) ξ p.1) *
        ((p.2 : ℂ) ^ m * gaussPhase (Real.exp t) η p.2)
        ∂(volume : Measure ℝ).prod volume) =
      gaussMoment (Real.exp s) n ξ * gaussMoment (Real.exp t) m η :=
    integral_prod_mul (fun x : ℝ => (x : ℂ) ^ n * gaussPhase (Real.exp s) ξ x)
      (fun y : ℝ => (y : ℂ) ^ m * gaussPhase (Real.exp t) η y)
  rw [integral_sub hsum (h 0 0),
    integral_add ((h 2 0).const_mul (Real.exp s : ℂ)) ((h 0 2).const_mul (Real.exp t : ℂ)),
    integral_const_mul, integral_const_mul,
    hsep 2 0, hsep 0 2, hsep 0 0]
  change (Real.exp s : ℂ) * (gaussMoment (Real.exp s) 2 ξ * gaussMoment (Real.exp t) 0 η) +
    (Real.exp t : ℂ) * (gaussMoment (Real.exp s) 0 ξ * gaussMoment (Real.exp t) 2 η) -
    gaussMoment (Real.exp s) 0 ξ * gaussMoment (Real.exp t) 0 η = _
  rw [gaussian_exp_second_moment, gaussian_exp_second_moment]
  have hs : (Real.exp s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s)
  have ht : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  push_cast
  field_simp
  ring

/-- The zero-frequency cancellation is genuinely two-dimensional. -/
theorem gaussianPlaneDefect_zero_mean (s t : ℝ) :
    (∫ p : ℝ × ℝ, gaussianPlaneDefect s t 0 0 p) = 0 := by
  rw [gaussianPlaneDefect_integral]
  simp

/-- Restricting to one dimension leaves a nonzero half-mass defect. -/
theorem gaussian_line_defect (s : ℝ) :
    (∫ x : ℝ, ((Real.exp s : ℂ) * (x : ℂ) ^ 2 - 1) *
      gaussPhase (Real.exp s) 0 x) = -(1 / 2 : ℂ) * gaussMoment (Real.exp s) 0 0 := by
  have h0 := integrable_gaussMomentIntegrand (Real.exp_pos s) 0 0
  have h2 := integrable_gaussMomentIntegrand (Real.exp_pos s) 2 0
  have heq : (fun x : ℝ => ((Real.exp s : ℂ) * (x : ℂ) ^ 2 - 1) *
      gaussPhase (Real.exp s) 0 x) = fun x : ℝ =>
      (Real.exp s : ℂ) * ((x : ℂ) ^ 2 * gaussPhase (Real.exp s) 0 x) -
      (x : ℂ) ^ 0 * gaussPhase (Real.exp s) 0 x := by
    funext x
    ring
  rw [heq, integral_sub (h2.const_mul _) h0, integral_const_mul]
  change (Real.exp s : ℂ) * gaussMoment (Real.exp s) 2 0 -
    gaussMoment (Real.exp s) 0 0 = _
  rw [gaussMoment_two_eq (Real.exp_pos s)]
  have hs : (Real.exp s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s)
  push_cast
  field_simp
  ring

/-- The one-dimensional defect is strictly negative, so the lost cancellation is detectable. -/
theorem gaussian_line_defect_re_neg (s : ℝ) :
    (∫ x : ℝ, ((Real.exp s : ℂ) * (x : ℂ) ^ 2 - 1) *
      gaussPhase (Real.exp s) 0 x).re < 0 := by
  rw [gaussian_line_defect, gaussMoment_zero_freq (Real.exp_pos s), gaussJetPoly_zero]
  simp only [pow_zero, one_mul, Polynomial.eval_one, Complex.ofReal_one, mul_one]
  have heq : -(1 / 2 : ℂ) * (Real.sqrt (Real.pi / Real.exp s) : ℂ) =
      ((-(1 / 2 * Real.sqrt (Real.pi / Real.exp s)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.ofReal_re]
  exact neg_neg_of_pos (mul_pos (one_div_pos.mpr zero_lt_two)
    (Real.sqrt_pos.mpr (div_pos Real.pi_pos (Real.exp_pos s))))

#print axioms gaussian_exp_second_moment
#print axioms gaussianPlaneDefect_integrable
#print axioms gaussianPlaneDefect_integral
#print axioms gaussianPlaneDefect_zero_mean
#print axioms gaussian_line_defect
#print axioms gaussian_line_defect_re_neg

end HilbertMetric
