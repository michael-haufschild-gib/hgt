import GaloisForLFunctions.RHTower.EntireExponentialMomentPolynomialDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian-window polynomial density

The finite measure `exp (-tau*x^2) dx`, for `tau > 0`, has a bilateral moment-generating
function on the whole real axis.  The general entire-exponential-moment theorem therefore makes
real polynomials dense in its `L²` space.

The proof of the exponential window uses the exact completion-of-the-square majorant

`exp (t*x - tau*x^2) <= exp (t^2/(2*tau)) * exp (-(tau/2)*x^2)`.

No Gaussian integral value is used; only integrability and `tau > 0` matter.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RHTower

/-- The unnormalised Gaussian window measure `exp (-tau*x^2) dx`. -/
def gaussianWindowMeasure (tau : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-tau * x ^ 2))

theorem gaussianWindowMeasure_finite {tau : ℝ} (htau : 0 < tau) :
    IsFiniteMeasure (gaussianWindowMeasure tau) := by
  unfold gaussianWindowMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_exp_neg_mul_sq htau).hasFiniteIntegral

/-- Completion of the square in the one-sided form used for Gaussian domination. -/
theorem linear_sub_gaussian_le_half_gaussian (tau t x : ℝ) (htau : 0 < tau) :
    t * x - tau * x ^ 2 ≤ t ^ 2 / (2 * tau) - (tau / 2) * x ^ 2 := by
  have hdiv : 0 ≤ (tau * x - t) ^ 2 / (2 * tau) :=
    div_nonneg (sq_nonneg (tau * x - t)) (by positivity)
  have hid : (tau * x - t) ^ 2 / (2 * tau) =
      (tau / 2) * x ^ 2 - t * x + t ^ 2 / (2 * tau) := by
    field_simp [ne_of_gt htau]
    ring
  rw [hid] at hdiv
  linarith

/-- Every real exponential is integrable against a positive Gaussian window. -/
theorem integrable_exp_mul_gaussianWindowMeasure {tau : ℝ} (htau : 0 < tau) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianWindowMeasure tau) := by
  unfold gaussianWindowMeasure
  rw [integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop : AEMeasurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-tau * x ^ 2))) volume)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have hmajor : Integrable (fun x : ℝ =>
      Real.exp (t ^ 2 / (2 * tau)) * Real.exp (-(tau / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (half_pos htau)).const_mul _
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards with x
  change |Real.exp (-tau * x ^ 2) * Real.exp (t * x)| ≤
    Real.exp (t ^ 2 / (2 * tau)) * Real.exp (-(tau / 2) * x ^ 2)
  rw [abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := linear_sub_gaussian_le_half_gaussian tau t x htau
  linarith

/-- A positive Gaussian window has an entire bilateral moment-generating window. -/
theorem gaussianWindowMeasure_hasEntireExponentialMoments
    {tau : ℝ} (htau : 0 < tau) :
    HasEntireExponentialMoments (gaussianWindowMeasure tau) := by
  apply Set.eq_univ_of_forall
  intro t
  exact integrable_exp_mul_gaussianWindowMeasure htau t

/-- **Gaussian polynomial density.** Real polynomials are dense in the `L²` space of every
positive Gaussian window. -/
theorem gaussianWindow_realMonomialSpan_closure_eq_top
    {tau : ℝ} (htau : 0 < tau) :
    letI := gaussianWindowMeasure_finite htau
    (realMonomialSpan (gaussianWindowMeasure tau)
      (gaussianWindowMeasure_hasEntireExponentialMoments htau)).topologicalClosure = ⊤ := by
  letI := gaussianWindowMeasure_finite htau
  exact realMonomialSpan_closure_eq_top _
    (gaussianWindowMeasure_hasEntireExponentialMoments htau)

end RHTower
