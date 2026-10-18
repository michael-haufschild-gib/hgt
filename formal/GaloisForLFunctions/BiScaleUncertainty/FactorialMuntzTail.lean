import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzCompletion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative control of the exact tail omitted by the compact factorial ramp. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialMuntzTail (n : ℕ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (factorialMuntzCompletion n)

/-- The completion error is exactly the negative-logarithmic tail. -/
theorem factorialMuntzCompletion_sub_ramp (n : ℕ) (x : ℝ) :
    factorialMuntzCompletion n x-sourceFactorialRamp (n+1) x = factorialMuntzTail n x := by
  by_cases hx : x ≤ 0
  · rw [factorialMuntzTail, indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      sourceFactorialRamp_zero_of_nonpos (by omega : 1 ≤ n+1) hx, sub_zero]
  · rw [factorialMuntzTail, indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      factorialMuntzCompletion_eq_ramp n (le_of_lt (lt_of_not_ge hx)), sub_self]

theorem factorialMuntzTail_measurable (n : ℕ) : Measurable (factorialMuntzTail n) :=
  (factorialMuntzCompletion_measurable n).indicator measurableSet_Iic

private def tailEnvelope (n : ℕ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun x => 100*Real.exp x/((n+1 : ℕ) : ℝ))

private theorem tailEnvelope_integrable (n : ℕ) : Integrable (tailEnvelope n) :=
  IntegrableOn.integrable_indicator
    (((integrableOn_exp_Iic 0).const_mul 100).div_const _) measurableSet_Iic

private theorem tailEnvelope_integral (n : ℕ) :
    (∫ x : ℝ, tailEnvelope n x) = 100/((n+1 : ℕ) : ℝ) := by
  rw [tailEnvelope, integral_indicator measurableSet_Iic, integral_div, integral_const_mul,
    integral_exp_Iic_zero, mul_one]

private theorem tail_sq_le (n : ℕ) (x : ℝ) : (factorialMuntzTail n x)^2 ≤ tailEnvelope n x := by
  by_cases hx : x ≤ 0
  · rw [factorialMuntzTail, tailEnvelope,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    have h := factorialMuntzCompletion_abs_le n x
    have hp : 0 ≤ 10*Real.exp (x/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
    have hh := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hp (abs_nonneg (factorialMuntzCompletion n x)))
    have he : (10*Real.exp (x/2)/Real.sqrt ((n+1 : ℕ) : ℝ))^2 =
        100*Real.exp x/((n+1 : ℕ) : ℝ) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have he2 : Real.exp (x/2)^2 = Real.exp x := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [he2]
      norm_num
    nlinarith [sq_abs (factorialMuntzCompletion n x)]
  · simp only [factorialMuntzTail, tailEnvelope,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), zero_pow (by omega : 2 ≠ 0), le_refl]

theorem factorialMuntzTail_sq_integrable (n : ℕ) :
    Integrable (fun x : ℝ => (factorialMuntzTail n x)^2) := by
  apply (tailEnvelope_integrable n).mono' ((factorialMuntzTail_measurable n).pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact tail_sq_le n x

/-- Uniform arithmetic cancellation gives a quantitative square-mass estimate
for the entire omitted half-line, with no zeta or discrepancy premise. -/
theorem factorialMuntzTail_sq_integral_le (n : ℕ) :
    (∫ x : ℝ, (factorialMuntzTail n x)^2) ≤ 100/((n+1 : ℕ) : ℝ) := by
  rw [← tailEnvelope_integral n]
  exact integral_mono (factorialMuntzTail_sq_integrable n) (tailEnvelope_integrable n) (tail_sq_le n)

/-- The actual compact ramp approximates its explicit arithmetic completion
with squared L² error at most `100/(n+1)`. -/
theorem factorialMuntzCompletion_sq_error_le (n : ℕ) :
    (∫ x : ℝ, (factorialMuntzCompletion n x-sourceFactorialRamp (n+1) x)^2) ≤
      100/((n+1 : ℕ) : ℝ) := by
  simp only [factorialMuntzCompletion_sub_ramp]
  exact factorialMuntzTail_sq_integral_le n

theorem factorialMuntzCompletion_sq_error_tendsto :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      (factorialMuntzCompletion n x-sourceFactorialRamp (n+1) x)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => 100/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hn).const_mul (100 : ℝ)
  exact squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _))
    factorialMuntzCompletion_sq_error_le hi

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
