import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailPhase

/-! Weighted square-mass control for the actual correction tail on a fixed
strip containing the entire nontrivial zeta divisor in its interior. -/

open MeasureTheory Set
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- Real parts on the fixed enlarged sampling strip. -/
abbrev FactorialSamplingAbscissa := Icc (-1/4 : ℝ) (5/4)

/-- The physical profile whose Fourier transform is the tail Mellin readout. -/
def factorialWeightedTail (n : ℕ) (σ x : ℝ) : ℝ :=
  Real.exp ((σ-1/2)*x)*factorialMuntzCorrectedTail n x

theorem factorialWeightedTail_measurable (n : ℕ) (σ : ℝ) :
    Measurable (factorialWeightedTail n σ) := by
  have hc : Continuous (fun x : ℝ => Real.exp ((σ-1/2)*x)) := by fun_prop
  exact hc.measurable.mul (factorialMuntzCorrectedTail_measurable n)

/-- Mellin tilting changes the decay exponent but retains the literal arithmetic phase. -/
theorem factorialWeightedTail_eq_phase (n : ℕ) (σ x : ℝ) :
    factorialWeightedTail n σ x = (Iic (0 : ℝ)).indicator
      (fun y => factorialTailAmplitude n*Real.exp ((σ+1)*y)*factorialTailPhase n y) x := by
  unfold factorialWeightedTail
  rw [factorialMuntzCorrectedTail_eq_phase]
  by_cases hx : x ≤ 0
  · simp only [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    have he : Real.exp ((σ-1/2)*x)*Real.exp (3*x/2) = Real.exp ((σ+1)*x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = factorialTailAmplitude n*(Real.exp ((σ-1/2)*x)*Real.exp (3*x/2))*
          factorialTailPhase n x := by ring
      _ = _ := by rw [he]
  · simp only [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),mul_zero]

/-- A square envelope valid for every Mellin weight; integrability is handled separately. -/
theorem factorialWeightedTail_sq_le (n : ℕ) (σ x : ℝ) :
    (factorialWeightedTail n σ x)^2 ≤ (Iic (0 : ℝ)).indicator
      (fun y => 144*Real.exp ((2*(σ+1))*y)/((n+1 : ℕ) : ℝ)) x := by
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  by_cases hx : x ≤ 0
  · have ht := factorialMuntzCorrectedTail_abs_le n x
    rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)] at ht ⊢
    have he : Real.exp ((σ-1/2)*x)*Real.exp (3*x/2) = Real.exp ((σ+1)*x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hb : |factorialWeightedTail n σ x| ≤
        12*Real.exp ((σ+1)*x)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
      unfold factorialWeightedTail
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp ((σ-1/2)*x)*(12*Real.exp (3*x/2)/Real.sqrt ((n+1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
        _ = _ := by
          calc
            _ = 12*(Real.exp ((σ-1/2)*x)*Real.exp (3*x/2))/
                Real.sqrt ((n+1 : ℕ) : ℝ) := by ring
            _ = _ := by rw [he]
    have he2 : (12*Real.exp ((σ+1)*x)/Real.sqrt ((n+1 : ℕ) : ℝ))^2 =
        144*Real.exp ((2*(σ+1))*x)/((n+1 : ℕ) : ℝ) := by
      rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
      have hx2 : Real.exp ((σ+1)*x)^2 = Real.exp ((2*(σ+1))*x) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      rw [hx2]
      norm_num
    calc
      _ = |factorialWeightedTail n σ x|^2 := (sq_abs _).symm
      _ ≤ (12*Real.exp ((σ+1)*x)/Real.sqrt ((n+1 : ℕ) : ℝ))^2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
      _ = _ := he2
  · simp only [factorialWeightedTail,factorialMuntzCorrectedTail,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),mul_zero,
      zero_pow (by omega : 2 ≠ 0),le_refl]

private theorem square_envelope_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable ((Iic (0 : ℝ)).indicator
      (fun x => 144*Real.exp ((2*((σ : ℝ)+1))*x)/((n+1 : ℕ) : ℝ))) := by
  have hb : 0 < 2*((σ : ℝ)+1) := by have := σ.2.1; linarith
  exact IntegrableOn.integrable_indicator
    (((integrableOn_exp_mul_Iic hb 0).const_mul 144).div_const _) measurableSet_Iic

/-- Every weight on the enlarged strip has finite squared physical mass. -/
theorem factorialWeightedTail_sq_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (fun x : ℝ => factorialWeightedTail n σ x^2) := by
  apply (square_envelope_integrable n σ).mono'
    ((factorialWeightedTail_measurable n σ).pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact factorialWeightedTail_sq_le n σ x

/-- The entire enlarged strip has a uniform square-mass budget of order `1/(n+1)`. -/
theorem factorialWeightedTail_sq_integral_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ x : ℝ, factorialWeightedTail n σ x^2) ≤ 96/((n+1 : ℕ) : ℝ) := by
  have hb : 0 < 2*((σ : ℝ)+1) := by have := σ.2.1; linarith
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ∫ x : ℝ, (Iic (0 : ℝ)).indicator
        (fun y => 144*Real.exp ((2*((σ : ℝ)+1))*y)/((n+1 : ℕ) : ℝ)) x :=
      integral_mono (factorialWeightedTail_sq_integrable n σ)
        (square_envelope_integrable n σ) (factorialWeightedTail_sq_le n σ)
    _ = 144/((2*((σ : ℝ)+1))*((n+1 : ℕ) : ℝ)) := by
      rw [integral_indicator measurableSet_Iic,integral_div,integral_const_mul,
        integral_exp_mul_Iic hb]
      simp only [mul_zero,Real.exp_zero,div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ 96/((n+1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hN).2
      have hlo := mul_le_mul_of_nonneg_right σ.2.1 hN.le
      nlinarith

end
end GaloisForLFunctions.ArithmeticPositivityTheory
