import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentOperator

/-! # Uniform finite-frequency approximation of the complete signed source -/

namespace RHTower.PaperPrimeArch
noncomputable section
open GaloisForLFunctions.HTGeometry MeasureTheory Filter Set
open scoped Topology NNReal

def cutoffSymbol (a : Height) (R : ℝ≥0) : ℝ → ℂ :=
  (Icc (-(R : ℝ)) R).indicator fun x => (current a x : ℂ)

theorem measurable_cutoffSymbol (a : Height) (R : ℝ≥0) : Measurable (cutoffSymbol a R) :=
  (Complex.continuous_ofReal.comp (continuous_current a)).measurable.indicator measurableSet_Icc

theorem norm_cutoffSymbol_le (a : Height) (R : ℝ≥0) (x : ℝ) :
    ‖cutoffSymbol a R x‖ ≤ decayBudget := by
  by_cases hx : x ∈ Icc (-(R : ℝ)) R
  · simpa only [cutoffSymbol, indicator_of_mem hx] using norm_current_le a x
  · simpa only [cutoffSymbol, indicator_of_notMem hx, norm_zero] using decayBudget_nonneg

def cutoffOperator (a : Height) (R : ℝ≥0) : Space →L[ℂ] Space :=
  lpBoundedMulCLM (measurable_cutoffSymbol a R) decayBudget_nonneg (norm_cutoffSymbol_le a R)

theorem cutoffOperator_apply_ae (a : Height) (R : ℝ≥0) (f : Space) :
    (cutoffOperator a R f : ℝ → ℂ) =ᵐ[volume] fun x => cutoffSymbol a R x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem norm_current_sub_cutoffSymbol_le (a : Height) (R : ℝ≥0) (x : ℝ) :
    ‖(current a x : ℂ) - cutoffSymbol a R x‖ ≤
      decayBudget * Real.exp (-(Real.pi / 4 * (R : ℝ))) := by
  by_cases hx : x ∈ Icc (-(R : ℝ)) R
  · simp only [cutoffSymbol, indicator_of_mem hx, sub_self, norm_zero]
    exact mul_nonneg decayBudget_nonneg (Real.exp_pos _).le
  · simp only [cutoffSymbol, indicator_of_notMem hx, sub_zero,
      Complex.norm_real, Real.norm_eq_abs]
    apply (abs_current_le_decay a x).trans
    have hr : (R : ℝ) < |x| := lt_of_not_ge fun h => hx (abs_le.mp h)
    apply mul_le_mul_of_nonneg_left _ decayBudget_nonneg
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hr.le (by positivity))

theorem norm_operator_sub_cutoff_le (a : Height) (R : ℝ≥0) :
    ‖operator a - cutoffOperator a R‖ ≤
      decayBudget * Real.exp (-(Real.pi / 4 * (R : ℝ))) := by
  apply norm_le_of_ae_mul (mul_nonneg decayBudget_nonneg (Real.exp_pos _).le)
    (norm_current_sub_cutoffSymbol_le a R)
  intro f
  filter_upwards [Lp.coeFn_sub (operator a f) (cutoffOperator a R f),
    operator_apply_ae a f, cutoffOperator_apply_ae a R f] with x hsub hA hC
  change (operator a f - cutoffOperator a R f : Space) x = _
  rw [hsub, Pi.sub_apply, hA, hC, sub_mul]

theorem cutoff_error_tendsto :
    Tendsto (fun n : ℕ => decayBudget * Real.exp (-(Real.pi / 4 * (n : ℝ))))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.pi / 4 * (n : ℝ)) atTop atTop := by
    simpa only [mul_comm] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (show 0 < Real.pi / 4 by positivity)
  simpa only [mul_zero, Function.comp_apply] using
    (tendsto_const_nhds (x := decayBudget)).mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht)

theorem cutoffOperator_tendsto (a : Height) :
    Tendsto (fun n : ℕ => cutoffOperator a n) atTop (𝓝 (operator a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
    (Filter.Eventually.of_forall fun n => ?_) cutoff_error_tendsto
  simpa only [norm_sub_rev, NNReal.coe_natCast] using norm_operator_sub_cutoff_le a n

end
end RHTower.PaperPrimeArch
