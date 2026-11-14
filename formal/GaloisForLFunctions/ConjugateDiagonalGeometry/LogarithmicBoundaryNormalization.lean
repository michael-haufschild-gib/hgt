import GaloisForLFunctions.ConjugateDiagonalGeometry.LogarithmicConvolution

/-!
# Normalizing logarithmic boundary estimates

An all-height epsilon estimate gives convergence after division by `log |t|`.
Continuity fills the compact interval omitted by an eventual logarithmic bound.
-/

open Filter Topology MeasureTheory Complex Set

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Uniform epsilon estimates at both signs of the height give a logarithmic
asymptotic in the absolute-height filter. -/
theorem tendsto_log_normalized_of_epsilon_bound {f : ℝ → ℂ} {L : ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖f t - (Real.log |t| : ℂ) * L‖ ≤ ε * Real.log |t|) :
    Tendsto (fun t => f t / (Real.log |t| : ℂ))
      (Filter.comap abs atTop) (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT,hb⟩ := h (ε/2) (by positivity)
  have habs : Tendsto (abs : ℝ → ℝ) (Filter.comap abs atTop) atTop :=
    Filter.tendsto_comap
  filter_upwards [habs.eventually (eventually_ge_atTop T)] with t ht
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith only [hT,ht])
  have hlogC : (Real.log |t| : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have he : f t / (Real.log |t| : ℂ) - L =
      (f t - (Real.log |t| : ℂ) * L) / (Real.log |t| : ℂ) := by
    field_simp <;> ring
  rw [dist_eq_norm,he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  have hh := div_le_div_of_nonneg_right (hb t ht) hlog.le
  rw [mul_div_cancel_right₀ _ hlog.ne'] at hh
  exact hh.trans_lt (by linarith only [hε])

/-- A continuous function with an eventual logarithmic bound has a global
majorant on the nonsingular scale `log (2 + |t|)`. -/
theorem exists_global_logarithmic_bound_of_eventual {f : ℝ → ℂ} {K : ℝ}
    (hf : Continuous f) (hK : 0 ≤ K)
    (h : ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ K * Real.log |t|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖f t‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨T,hT,hb⟩ := h
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (-T) T))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|B| / Real.log 2 + K,by positivity,fun t => ?_⟩
  have hl : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_right (abs_nonneg t))
  have hl0 : 0 ≤ Real.log (2 + |t|) := hl2.le.trans hl
  rcases le_or_gt |t| T with ht | ht
  · have hbt : ‖f t‖ ≤ |B| := (hB t (abs_le.mp ht)).trans (le_abs_self B)
    have hm := mul_le_mul_of_nonneg_left hl (div_nonneg (abs_nonneg B) hl2.le)
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    have hk := mul_nonneg hK hl0
    nlinarith only [hbt,hm,hk]
  · have ht0 : 0 < |t| := by linarith only [hT,ht]
    have hlog := Real.log_le_log ht0 (show |t| ≤ 2 + |t| by linarith)
    have hh := (hb t ht.le).trans (mul_le_mul_of_nonneg_left hlog hK)
    have hm := mul_nonneg (div_nonneg (abs_nonneg B) hl2.le) hl0
    nlinarith only [hh,hm]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_log_normalized_of_epsilon_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_global_logarithmic_bound_of_eventual
