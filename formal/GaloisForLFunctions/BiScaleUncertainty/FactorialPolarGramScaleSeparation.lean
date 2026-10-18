import GaloisForLFunctions.BiScaleUncertainty.FactorialPolarLossLowerBound
import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilMixedDecay

/-! The actual polar loss dominates the existing mixed-Gram error. This closes
the proposed polar-absorption shortcut with a quantitative positive survivor. -/

open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem factorialWeilGramError_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)*factorialWeilGramError n) atTop (𝓝 0) := by
  have he : (fun n : ℕ => ((n+1 : ℕ) : ℝ)*factorialWeilGramError n) =
      fun n => (1/2 : ℝ)*(factorialWeilMixedBound n)^2 := by
    funext n
    unfold factorialWeilGramError
    field_simp
  rw [he]
  simpa using (factorialWeilMixedBound_tendsto.pow 2).const_mul (1/2 : ℝ)

private theorem gram_div_polar_le (n : ℕ) :
    factorialWeilGramError n/factorialPolarLoss n ≤
      (8/Real.log 2)*(((n+1 : ℕ) : ℝ)*factorialWeilGramError n) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 ≤ factorialWeilGramError n := by unfold factorialWeilGramError; positivity
  have hbase := factorialPolarLoss_scaled_lower n
  apply (div_le_iff₀ (factorialPolarLoss_pos n)).2
  calc
    _ = ((8/Real.log 2)*factorialWeilGramError n)*(Real.log 2/8) := by field_simp
    _ ≤ ((8/Real.log 2)*factorialWeilGramError n)*
        (((n+1 : ℕ) : ℝ)*factorialPolarLoss n) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring

/-- The error-to-loss ratio tends to zero for the actual factorial source family. -/
theorem factorialWeilGramError_div_polarLoss_tendsto :
    Tendsto (fun n : ℕ => factorialWeilGramError n/factorialPolarLoss n) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ =>
      (8/Real.log 2)*(((n+1 : ℕ) : ℝ)*factorialWeilGramError n)) atTop (𝓝 0) := by
    simpa using factorialWeilGramError_scaled_tendsto.const_mul (8/Real.log 2)
  apply squeeze_zero (fun n => ?_) gram_div_polar_le hb
  exact div_nonneg (by unfold factorialWeilGramError; positivity) (factorialPolarLoss_pos n).le

theorem factorialWeilGramError_eventually_lt_polarLoss :
    ∀ᶠ n : ℕ in atTop, factorialWeilGramError n < factorialPolarLoss n := by
  have h : ∀ᶠ n : ℕ in atTop, factorialWeilGramError n/factorialPolarLoss n < (1 : ℝ) :=
    Filter.Tendsto.eventually_lt_const (by norm_num) factorialWeilGramError_div_polarLoss_tendsto
  filter_upwards [h] with n hn
  simpa only [one_mul] using (div_lt_iff₀ (factorialPolarLoss_pos n)).1 hn

/-- The existing Gram-error budget cannot eventually absorb the actual pole. -/
theorem not_eventually_factorialPolarLoss_le_gramError :
    ¬ (∀ᶠ n : ℕ in atTop, factorialPolarLoss n ≤ factorialWeilGramError n) := by
  intro h
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [factorialWeilGramError_eventually_lt_polarLoss, h] with n hn hn'
    linarith
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
