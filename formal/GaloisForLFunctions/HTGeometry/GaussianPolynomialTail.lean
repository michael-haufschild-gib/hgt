import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Polynomial weights against the Gaussian: integrability and tails

`(1+|v|)^M ≤ exp(M² + v²/4)` for every natural `M`, so `(1+|v|)^M e^{-v²}` is integrable, and its
integral over `{|v| > V}` is at most `e^{M²} e^{-V²/2} √(4π)`: the Gaussian tail beats every fixed
polynomial weight, with an explicit constant.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem one_add_abs_pow_le_exp (M : ℕ) (v : ℝ) :
    (1 + |v|) ^ M ≤ Real.exp (M ^ (2 : ℕ) + v ^ (2 : ℕ) / 4) := by
  have h1 : 1 + |v| ≤ Real.exp |v| := by linarith [Real.add_one_le_exp |v|]
  calc (1 + |v|) ^ M ≤ (Real.exp |v|) ^ M := pow_le_pow_left₀ (by positivity) h1 M
    _ = Real.exp (M * |v|) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (M ^ (2 : ℕ) + v ^ (2 : ℕ) / 4) := by
        apply Real.exp_le_exp.mpr
        have := sq_abs v
        nlinarith [sq_nonneg ((M : ℝ) - |v| / 2)]

theorem one_add_abs_pow_mul_exp_neg_sq_le (M : ℕ) (v : ℝ) :
    (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ))) ≤ Real.exp (M ^ (2 : ℕ)) * Real.exp (-(3 / 4) * v ^ (2 : ℕ)) := by
  calc (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))
      ≤ Real.exp (M ^ (2 : ℕ) + v ^ (2 : ℕ) / 4) * Real.exp (-(v ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right (one_add_abs_pow_le_exp M v) (by positivity)
    _ = Real.exp (M ^ (2 : ℕ)) * Real.exp (-(3 / 4) * v ^ (2 : ℕ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

theorem continuous_one_add_abs_pow_mul_exp_neg_sq (M : ℕ) :
    Continuous (fun v : ℝ => (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))) := by
  fun_prop

theorem integrable_one_add_abs_pow_mul_exp_neg_sq (M : ℕ) :
    Integrable (fun v : ℝ => (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 3 / 4)).const_mul
    (Real.exp (M ^ (2 : ℕ)))) (continuous_one_add_abs_pow_mul_exp_neg_sq M).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_add_abs_pow_mul_exp_neg_sq_le M v

/-- **Gaussian tail with a polynomial weight.** -/
theorem integral_one_add_abs_pow_mul_exp_neg_sq_compl_le (M : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    ∫ v in {v : ℝ | |v| ≤ V}ᶜ, (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))
      ≤ Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2) * Real.sqrt (4 * Real.pi) := by
  have hmeas : MeasurableSet {v : ℝ | |v| ≤ V}ᶜ :=
    (isClosed_le continuous_abs continuous_const).measurableSet.compl
  have hbound : ∀ v ∈ {v : ℝ | |v| ≤ V}ᶜ, (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))
      ≤ (Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2)) * Real.exp (-(1 / 4) * v ^ (2 : ℕ)) := by
    intro v hv
    have hv' : V < |v| := by
      simpa [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hv
    have hsq : V ^ (2 : ℕ) ≤ v ^ (2 : ℕ) := by
      rw [← sq_abs v]
      exact pow_le_pow_left₀ hV hv'.le 2
    refine (one_add_abs_pow_mul_exp_neg_sq_le M v).trans ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hint : Integrable (fun v : ℝ =>
      (Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2)) * Real.exp (-(1 / 4) * v ^ (2 : ℕ))) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  calc ∫ v in {v : ℝ | |v| ≤ V}ᶜ, (1 + |v|) ^ M * Real.exp (-(v ^ (2 : ℕ)))
      ≤ ∫ v in {v : ℝ | |v| ≤ V}ᶜ,
          (Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2)) * Real.exp (-(1 / 4) * v ^ (2 : ℕ)) :=
        setIntegral_mono_on (integrable_one_add_abs_pow_mul_exp_neg_sq M).integrableOn
          hint.integrableOn hmeas hbound
    _ ≤ ∫ v, (Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2)) * Real.exp (-(1 / 4) * v ^ (2 : ℕ)) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun v => by positivity)
    _ = Real.exp (M ^ (2 : ℕ)) * Real.exp (-(V ^ (2 : ℕ)) / 2) * Real.sqrt (4 * Real.pi) := by
        rw [integral_const_mul, integral_gaussian]
        congr 2
        rw [div_div_eq_mul_div, div_one, mul_comm]

/-- The full Gaussian mass on any set is at most `√π`. -/
theorem setIntegral_exp_neg_sq_le (s : Set ℝ) :
    ∫ v in s, Real.exp (-(v ^ (2 : ℕ))) ≤ Real.sqrt Real.pi := by
  have hint : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ)))) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  calc ∫ v in s, Real.exp (-(v ^ (2 : ℕ))) ≤ ∫ v, Real.exp (-(v ^ (2 : ℕ))) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun v => by positivity)
    _ = Real.sqrt Real.pi := by
        have := integral_gaussian 1
        simpa using this

end GaloisForLFunctions.HTGeometry
