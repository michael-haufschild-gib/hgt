import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.PolynomialPulses

/-! Finite polynomial translation averages multiply complex Laplace values by
the polynomial evaluated at the translation character. Negative-root repair
factors preserve every character in a sufficiently small phase strip. -/

open Polynomial MeasureTheory
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

theorem continuous_polynomialAverage (p : ℝ[X]) (h : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (polynomialAverage p h f) := by
  change Continuous (fun x => polynomialAverage p h f x)
  simp only [polynomialAverage_apply]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (hf.comp (continuous_id.sub continuous_const))

theorem integrable_polynomialAverage_exp (p : ℝ[X]) (h s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable fun x => f x * Real.exp (s * x)) :
    Integrable fun x => polynomialAverage p h f x * Real.exp (s * x) := by
  simp only [polynomialAverage_apply, Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum _ fun (i : ℕ) _ =>
    (integrable_translate_exp hf ((i : ℝ) * h)).const_mul _

theorem integrable_translate_cexp {f : ℝ → ℝ} {w : ℂ}
    (hf : Integrable fun x : ℝ => (f x : ℂ) * Complex.exp (w * x)) (t : ℝ) :
    Integrable fun x : ℝ => (f (x - t) : ℂ) * Complex.exp (w * x) := by
  refine ((hf.comp_sub_right t).const_mul (Complex.exp (w * t))).congr ?_
  filter_upwards [] with x
  simp only [mul_comm (Complex.exp (w * t)), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Polynomial translation multiplies every complex Laplace value by its evaluation
at the exponential translation character. -/
theorem integral_polynomialAverage_cexp (p : ℝ[X]) (h : ℝ) (w : ℂ) {f : ℝ → ℝ}
    (hf : Integrable fun x : ℝ => (f x : ℂ) * Complex.exp (w * x)) :
    (∫ x : ℝ, (polynomialAverage p h f x : ℂ) * Complex.exp (w * x)) =
      p.eval₂ (algebraMap ℝ ℂ) (Complex.exp (w * h)) *
        ∫ x : ℝ, (f x : ℂ) * Complex.exp (w * x) := by
  have hc (x : ℝ) : (polynomialAverage p h f x : ℂ) =
      ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (f (x - i * h) : ℂ) := by
    rw [polynomialAverage_apply]
    push_cast
    rfl
  simp_rw [hc, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun (i : ℕ) _ =>
    (integrable_translate_cexp hf ((i : ℝ) * h)).const_mul (p.coeff i : ℂ))]
  simp_rw [integral_const_mul]
  rw [eval₂_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have ht : (∫ x : ℝ, (f (x - (i : ℝ) * h) : ℂ) * Complex.exp (w * x)) =
      Complex.exp (w * ((i : ℝ) * h)) * ∫ x : ℝ, (f x : ℂ) * Complex.exp (w * x) := by
    rw [← integral_add_right_eq_self
      (fun x : ℝ => (f (x - (i : ℝ) * h) : ℂ) * Complex.exp (w * x)) ((i : ℝ) * h)]
    simp_rw [add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    push_cast
    ring
  have he : Complex.exp (w * ((i : ℝ) * h)) = Complex.exp (w * h) ^ i := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [ht, he]
  change _ = ((p.coeff i : ℂ) * _) * _
  ring

/-- Negative-root correcting multipliers cannot erase characters in this phase strip. -/
theorem negativeRootMultiplier_eval₂_exp_ne_zero {r : List ℝ} (hr : ∀ a ∈ r, 0 < a)
    {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    (negativeRootMultiplier r).eval₂ (algebraMap ℝ ℂ) (Complex.exp w) ≠ 0 := by
  apply negativeRootMultiplier_eval₂_ne_zero hr
  rw [Complex.exp_re]
  apply (mul_pos (Real.exp_pos _) ?_).le
  apply Real.cos_pos_of_mem_Ioo
  have hh := abs_lt.mp hw
  exact ⟨by linarith only [hh.1], hh.2⟩

#print axioms integral_polynomialAverage_cexp
#print axioms negativeRootMultiplier_eval₂_exp_ne_zero
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
