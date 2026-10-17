import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceFactorization
import GaloisForLFunctions.BiScaleUncertainty.ExponentialTentSourceEnergy

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

private theorem integrable_source_sq (f : C_c(ℝ, ℝ)) : Integrable (fun u => (f u)^2) := by
  have hc : Continuous (fun u : ℝ => f u) := f.continuous
  apply (hc.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using f.hasCompactSupport.mul_left (f := (f : ℝ → ℝ))

private theorem factorialSourceScale_inv_sq (n : ℕ) :
    ((factorialSourceScale n)⁻¹)^2 = 1/Real.sqrt (n+1 : ℕ) := by
  rw [← factorialSourceScale_sq n]
  have hs := (factorialSourceScale_pos n).ne'
  field_simp

theorem factorialSourcePlus_energy (n : ℕ) :
    autocorr (factorialSourcePlus n) 0 =
      Real.sqrt (n+1 : ℕ)*(∫ u : ℝ, (factorialSourceLeft n u)^2)+
        (∫ u : ℝ, (factorialSourceRight n u)^2)/Real.sqrt (n+1 : ℕ) := by
  have hiL : Integrable (fun u => Real.sqrt (n+1 : ℕ)*(factorialSourceLeft n u)^2) :=
    (integrable_source_sq _).const_mul _
  have hiR : Integrable (fun u => (factorialSourceRight n u)^2/Real.sqrt (n+1 : ℕ)) :=
    (integrable_source_sq _).div_const _
  unfold autocorr
  calc
    _ = ∫ u : ℝ, Real.sqrt (n+1 : ℕ)*(factorialSourceLeft n u)^2+
        (factorialSourceRight n u)^2/Real.sqrt (n+1 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [add_zero]
      change (factorialSourceScale n*factorialSourceLeft n u+(factorialSourceScale n)⁻¹*factorialSourceRight n u)*
        (factorialSourceScale n*factorialSourceLeft n u+(factorialSourceScale n)⁻¹*factorialSourceRight n u) = _
      calc
        _ = (factorialSourceScale n)^2*(factorialSourceLeft n u)^2+
            ((factorialSourceScale n)⁻¹)^2*(factorialSourceRight n u)^2 +
              2*(factorialSourceScale n*(factorialSourceScale n)⁻¹)*(factorialSourceLeft n u*factorialSourceRight n u) := by ring
        _ = _ := by
          rw [factorialSource_disjoint, mul_zero, add_zero, factorialSourceScale_sq, factorialSourceScale_inv_sq]
          ring
    _ = _ := by rw [integral_add hiL hiR, integral_const_mul, integral_div]

theorem factorialSourceMinus_energy (n : ℕ) :
    autocorr (factorialSourceMinus n) 0 =
      Real.sqrt (n+1 : ℕ)*(∫ u : ℝ, (factorialSourceLeft n u)^2)+
        (∫ u : ℝ, (factorialSourceRight n u)^2)/Real.sqrt (n+1 : ℕ) := by
  have hiL : Integrable (fun u => Real.sqrt (n+1 : ℕ)*(factorialSourceLeft n u)^2) :=
    (integrable_source_sq _).const_mul _
  have hiR : Integrable (fun u => (factorialSourceRight n u)^2/Real.sqrt (n+1 : ℕ)) :=
    (integrable_source_sq _).div_const _
  unfold autocorr
  calc
    _ = ∫ u : ℝ, Real.sqrt (n+1 : ℕ)*(factorialSourceLeft n u)^2+
        (factorialSourceRight n u)^2/Real.sqrt (n+1 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [add_zero]
      change (factorialSourceScale n*factorialSourceLeft n u-(factorialSourceScale n)⁻¹*factorialSourceRight n u)*
        (factorialSourceScale n*factorialSourceLeft n u-(factorialSourceScale n)⁻¹*factorialSourceRight n u) = _
      calc
        _ = (factorialSourceScale n)^2*(factorialSourceLeft n u)^2+
            ((factorialSourceScale n)⁻¹)^2*(factorialSourceRight n u)^2 -
              2*(factorialSourceScale n*(factorialSourceScale n)⁻¹)*(factorialSourceLeft n u*factorialSourceRight n u) := by ring
        _ = _ := by
          rw [factorialSource_disjoint, mul_zero, sub_zero, factorialSourceScale_sq, factorialSourceScale_inv_sq]
          ring
    _ = _ := by rw [integral_add hiL hiR, integral_const_mul, integral_div]

theorem factorialSourceLeft_energy_le (n : ℕ) :
    (∫ u : ℝ, (factorialSourceLeft n u)^2) ≤ 16 := by
  change (∫ u : ℝ, (sourceFactorialRamp (n+1) (-u))^2) ≤ 16
  rw [integral_neg_eq_self (fun u => (sourceFactorialRamp (n+1) u)^2)]
  exact integral_rampBiNull_sq_le (sourceFactorialCollar_pos (by omega)) (by omega)
    (sourceFactorialCollar_budget (by omega))

theorem factorialSourceRight_energy_bounds (n : ℕ) :
    6*((n+1 : ℕ) : ℝ) ≤ (∫ u : ℝ, (factorialSourceRight n u)^2) ∧
      (∫ u : ℝ, (factorialSourceRight n u)^2) ≤ 30*((n+1 : ℕ) : ℝ) := by
  have hN : 1 ≤ n+1 := by omega
  have hd := sourceFactorialWidth_pos hN
  obtain ⟨hl,hu⟩ := sourceFactorial_width_cost hN
  constructor
  · exact hl.trans (exponentialTentSource_energy_lower hd)
  · change (∫ u : ℝ, (exponentialTentSource (sourceFactorialWidth (n+1)) u)^2) ≤ _
    apply (exponentialTentSource_energy_upper hd).trans
    apply le_trans _ hu
    exact div_le_div_of_nonneg_right (exp_four_sourceFactorialWidth_le_two hN) hd.le

/-- The reciprocal scaling preserves the mixed correlation and balances source cost
at square-root growth in the arithmetic cutoff. -/
theorem factorialSource_energy_certificate (n : ℕ) :
    autocorr (factorialSourcePlus n) 0 = autocorr (factorialSourceMinus n) 0 ∧
      6*Real.sqrt (n+1 : ℕ) ≤ autocorr (factorialSourcePlus n) 0 ∧
      autocorr (factorialSourcePlus n) 0 ≤ 46*Real.sqrt (n+1 : ℕ) := by
  rw [factorialSourcePlus_energy, factorialSourceMinus_energy]
  have hl0 : 0 ≤ ∫ u : ℝ, (factorialSourceLeft n u)^2 := integral_nonneg (fun u => sq_nonneg _)
  have hlu := factorialSourceLeft_energy_le n
  obtain ⟨hrl,hru⟩ := factorialSourceRight_energy_bounds n
  have hr : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hs : (Real.sqrt (n+1 : ℕ))^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hrl' : 6*Real.sqrt (n+1 : ℕ) ≤
      (∫ u : ℝ, (factorialSourceRight n u)^2)/Real.sqrt (n+1 : ℕ) :=
    (le_div_iff₀ hr).2 (by nlinarith)
  have hru' : (∫ u : ℝ, (factorialSourceRight n u)^2)/Real.sqrt (n+1 : ℕ) ≤
      30*Real.sqrt (n+1 : ℕ) := (div_le_iff₀ hr).2 (by nlinarith)
  refine ⟨rfl, ?_, ?_⟩
  · nlinarith [mul_nonneg hr.le hl0]
  · nlinarith [mul_le_mul_of_nonneg_left hlu hr.le]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
