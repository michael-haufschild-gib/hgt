import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilGram

/-! The pure factorial tent has no prime atoms and a growing full Weil diagonal. -/

open MeasureTheory Set Filter
open Zeta23
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

private theorem tent_nonneg (n : ℕ) (u : ℝ) : 0 ≤ factorialSourceRight n u := by
  change 0 ≤ exponentialTentSource (sourceFactorialWidth (n+1)) u
  rw [exponentialTentSource_eq]
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (causalTent_nonneg _ _)) (sq_nonneg _)

theorem factorialSourceRight_primeTerm_zero (n : ℕ) :
    primeTerm (autocorr (factorialSourceRight n)) = 0 := by
  funext j
  unfold primeTerm
  by_cases hj : 2 ≤ j
  · rw [if_pos hj, factorialSourceRight_autocorr_tail n, mul_zero]
    have hn : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
    have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
    have hw := (le_div_iff₀ (by positivity : (0 : ℝ) < 12*((n+1 : ℕ) : ℝ))).1
      (sourceFactorialWidth_bounds (by omega : 1 ≤ n+1)).2
    have hm : (2 : ℝ) ≤ j := by exact_mod_cast hj
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  · simp [hj]

theorem factorialSourceRight_fullPairing_nonpos (n : ℕ) :
    fullPairing (autocorr (factorialSourceRight n)) ≤ 0 := by
  unfold fullPairing
  rw [factorialSourceRight_primeTerm_zero]
  simp only [Pi.zero_apply, tsum_zero, zero_sub, neg_nonpos]
  apply integral_nonneg
  intro x
  apply mul_nonneg
  · unfold polarDensity
    positivity
  · unfold autocorr
    exact integral_nonneg fun u => mul_nonneg (tent_nonneg n u) (tent_nonneg n (u+x))

theorem factorialTentWeil_scaled_lower (n : ℕ) :
    6*Real.exp (-(1/2 : ℝ))*Real.log ((n+1 : ℕ) : ℝ)-30*|EF.gammaBracket 0| ≤
      factorialSpanWeil n 0 1/((n+1 : ℕ) : ℝ) := by
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hnp).2
  rw [factorialSpanWeil_eq_complete]
  simp only [zero_smul, one_smul, zero_add]
  have hR0 := autocorr_zero_nonneg (factorialSourceRight n)
  have hRhi := (factorialSourceRight_energy_bounds n).2
  rw [integral_sq_eq_autocorr_zero] at hRhi
  have hgamma := neg_abs_le (EF.gammaBracket 0)
  have hG := mul_le_mul_of_nonneg_right hgamma hR0
  have hA := mul_le_mul_of_nonneg_left hRhi (abs_nonneg (EF.gammaBracket 0))
  have hJ := factorialSourceRight_jump_energy_lower n
  have hP := factorialSourceRight_fullPairing_nonpos n
  nlinarith

theorem factorialTentWeil_scaled_tendsto :
    Tendsto (fun n => factorialSpanWeil n 0 1/((n+1 : ℕ) : ℝ)) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hl := (Real.tendsto_log_atTop.comp hn).const_mul_atTop
    (show 0 < (6 : ℝ)*Real.exp (-(1/2 : ℝ)) by positivity)
  apply tendsto_atTop_mono (fun n => factorialTentWeil_scaled_lower n)
  simpa only [Function.comp_def, sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-(30*|EF.gammaBracket 0|)) hl

theorem factorialTentWeil_eventually_ge_scale :
    ∀ᶠ n in atTop, ((n+1 : ℕ) : ℝ) ≤ factorialSpanWeil n 0 1 := by
  filter_upwards [factorialTentWeil_scaled_tendsto.eventually (eventually_ge_atTop 1)] with n hn
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  simpa using (le_div_iff₀ hnp).1 hn

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
