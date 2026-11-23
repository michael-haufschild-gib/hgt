import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.Arbitrary

/-! # Power-law trace budgets and the unique critical-line frontier -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set
open scoped NNReal

/-- Trace tolerance M/t^α at heights t ≥ 1, extended constantly below one. -/
def powerTraceBudget (M : ℝ≥0) (α t : ℝ) : ℝ≥0 :=
  ⟨(M:ℝ)/(max 1 t)^α,div_nonneg M.coe_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)⟩

/-- Every constant multiple of the indicated inverse power of height yields uniform vanishing. -/
def movingTraceStable (σ α : ℝ) : Prop := ∀ M : ℝ≥0, clockBudgetStable σ (powerTraceBudget M α)

private theorem rescaled_power_budget (M : ℝ≥0) (α q : ℝ) :
    (fun t : ℝ => t^q*(powerTraceBudget M α t:ℝ)) =ᶠ[atTop] (fun t => (M:ℝ)*t^(q-α)) := by
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  change t^q*((M:ℝ)/(max 1 t)^α) = _
  rw [max_eq_right ht,Real.rpow_sub (zero_lt_one.trans_le ht)]
  ring

private theorem power_budget_threshold (σ α : ℝ) :
    movingTraceStable σ α ↔ 0 < σ ∧ clockBudgetExponent σ < α := by
  constructor
  · intro h
    obtain ⟨hs,hl⟩ := (clockBudgetStable_iff _ _).mp (h 1)
    have he := hl.congr' (rescaled_power_budget 1 α (clockBudgetExponent σ))
    refine ⟨hs,?_⟩
    by_contra! hn
    obtain ⟨t,ht,hsmall⟩ := ((eventually_ge_atTop (1:ℝ)).and (he.eventually_lt_const zero_lt_one)).exists
    simp only [NNReal.coe_one,one_mul] at hsmall
    exact (Real.one_le_rpow ht (sub_nonneg.mpr hn)).not_gt hsmall
  · rintro ⟨hs,hl⟩ M
    apply (clockBudgetStable_iff _ _).mpr
    refine ⟨hs,?_⟩
    have he := (tendsto_rpow_neg_atTop (sub_pos.mpr hl)).const_mul (M:ℝ)
    rw [mul_zero] at he
    simp only [neg_sub] at he
    exact he.congr' (rescaled_power_budget M α (clockBudgetExponent σ)).symm

/-- Stability at real temperature σ and inverse power α requires α > 1 and either summability or ασ > 2. -/
theorem movingTraceStable_iff (σ α : ℝ) :
    movingTraceStable σ α ↔ 1 < α ∧ (1 < σ ∨ 2 < α*σ) := by
  rw [power_budget_threshold]
  by_cases hw : σ ≤ 1
  · simp only [clockBudgetExponent,if_pos hw]
    constructor
    · rintro ⟨hs,hq⟩
      exact ⟨((one_le_div hs).mpr (hw.trans (by norm_num))).trans_lt hq,Or.inr ((div_lt_iff₀ hs).mp hq)⟩
    · rintro ⟨hα,hh⟩
      have hp := hh.resolve_left (not_lt.mpr hw)
      have hs : 0 < σ := lt_of_not_ge (fun hn => (mul_nonpos_of_nonneg_of_nonpos (zero_lt_one.trans hα).le hn).not_gt
        ((by norm_num : (0:ℝ)<2).trans hp))
      exact ⟨hs,(div_lt_iff₀ hs).mpr hp⟩
  · have hs := lt_of_not_ge hw
    simp only [clockBudgetExponent,if_neg hw]
    exact ⟨fun h => ⟨h.2,Or.inl hs⟩,fun h => ⟨zero_lt_one.trans hs,h.1⟩⟩

/-- At every power above one the frontier is a vertical line. At lower powers there is no stable half-plane. -/
theorem moving_trace_frontier (s : ℂ) (α : ℝ) :
    s ∈ frontier {w : ℂ | movingTraceStable w.re α} ↔ 1 < α ∧ s.re = min 1 (2/α) := by
  by_cases hα : 1 < α
  · have hp := zero_lt_one.trans hα
    have he : {w : ℂ | movingTraceStable w.re α} = Complex.re ⁻¹' Ioi (min 1 (2/α)) := by
      ext w
      rw [mem_setOf_eq,movingTraceStable_iff,and_iff_right hα]
      change (1 < w.re ∨ 2 < α*w.re) ↔ min 1 (2/α) < w.re
      rw [min_lt_iff,div_lt_iff₀ hp,mul_comm α]
    rw [he,Complex.frontier_preimage_re,frontier_Ioi,mem_preimage,mem_singleton_iff,and_iff_right hα]
  · have he : {w : ℂ | movingTraceStable w.re α} = ∅ := by
      ext w
      simp only [mem_setOf_eq,movingTraceStable_iff,hα,false_and,mem_empty_iff_false]
    simp only [he,frontier_empty,mem_empty_iff_false,hα,false_and]

/-- Inverse-fourth decay locates the isometric composition line at the original amplitude temperature. -/
theorem split_isometric_iff_fourth_budget_frontier (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      s ∈ frontier {w : ℂ | movingTraceStable w.re 4} := by
  rw [split_isometric_iff,moving_trace_frontier]
  norm_num

/-- Four is the unique loss exponent whose stability frontier contains any isometric composition parameter. -/
theorem isometric_frontier_power_iff {s : ℂ}
    (hi : ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) (α : ℝ) :
    s ∈ frontier {w : ℂ | movingTraceStable w.re α} ↔ α = 4 := by
  have hs := (split_isometric_iff s).mp hi
  constructor
  · intro h
    obtain ⟨hα,he⟩ := (moving_trace_frontier s α).mp h
    rw [hs] at he
    rcases le_total 1 (2/α) with hl | hl
    · rw [min_eq_left hl] at he
      norm_num at he
    · rw [min_eq_right hl] at he
      have hmul := (eq_div_iff (zero_lt_one.trans hα).ne').mp he
      linarith only [hmul]
  · rintro rfl
    exact (split_isometric_iff_fourth_budget_frontier s).mp hi

#print axioms movingTraceStable_iff
#print axioms moving_trace_frontier
#print axioms split_isometric_iff_fourth_budget_frontier
#print axioms isometric_frontier_power_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
