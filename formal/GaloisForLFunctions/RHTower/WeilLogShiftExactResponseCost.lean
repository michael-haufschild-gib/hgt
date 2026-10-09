import GaloisForLFunctions.RHTower.WeilLogShiftSharpDualProfile

/-!
# Exact response cost in an arbitrary finite-dimensional amplitude norm

Compactness gives an attained dual norm without inner product structure.
The minimum norm realizing a scalar response is its magnitude divided by
the dual norm, provided the response is feasible. A single budget criterion
also handles zero functionals, trivial amplitude spaces, and negative budgets.
-/

open Metric

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A scalar functional attains its norm on the closed unit ball, including
the zero functional and the zero-dimensional amplitude space. -/
theorem exists_finiteDimensional_dual_norm_attainer (f : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ ≤ 1 ∧ |f v| = ‖f‖ := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    ⟨0, by simp⟩ f.continuous.norm.continuousOn
  have hv' : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
  refine ⟨v, hv', ?_⟩
  rw [← Real.norm_eq_abs]
  apply le_antisymm
  · simpa only [mul_one] using f.le_opNorm_of_le hv'
  · by_contra h
    obtain ⟨w, hw, hfw⟩ := f.exists_lt_apply_of_lt_opNorm (lt_of_not_ge h)
    exact (not_lt_of_ge (hmax (mem_closedBall_zero_iff.mpr hw.le))) hfw

/-- Feasibility and attained minimum cost, with no nonvanishing assumption
on the functional. An arbitrary norm need not give a unique minimizer. -/
theorem finiteDimensional_dual_minimum_response_iff (f : E →L[ℝ] ℝ) (r : ℝ) :
    (∃ a : E, f a = r ∧ ‖a‖ = |r| / ‖f‖ ∧
      ∀ b : E, f b = r → ‖a‖ ≤ ‖b‖) ↔ r = 0 ∨ 0 < ‖f‖ := by
  constructor
  · rintro ⟨a, ha, _, _⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr (norm_pos_iff.mpr ?_)
      intro hf
      apply hr
      simpa [hf] using ha.symm
  · rintro (rfl | hf)
    · refine ⟨0, map_zero f, ?_, fun b _ => ?_⟩
      · simp
      · simpa only [norm_zero] using norm_nonneg b
    · obtain ⟨v, hv, hfv⟩ := exists_finiteDimensional_dual_norm_attainer f
      have hv1 : ‖v‖ = 1 := by
        have hbound := f.le_opNorm v
        rw [Real.norm_eq_abs, hfv] at hbound
        nlinarith
      have hfv0 : f v ≠ 0 := by
        intro hzero
        rw [hzero, abs_zero] at hfv
        linarith
      let a : E := (r / f v) • v
      have ha : f a = r := by
        dsimp only [a]
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfv0]
      have hn : ‖a‖ = |r| / ‖f‖ := by
        dsimp only [a]
        rw [norm_smul, Real.norm_eq_abs, abs_div, hfv, hv1, mul_one]
      refine ⟨a, ha, hn, ?_⟩
      intro b hb
      rw [hn]
      apply (div_le_iff₀ hf).mpr
      have hbound := f.le_opNorm b
      rw [Real.norm_eq_abs, hb] at hbound
      simpa only [mul_comm] using hbound

/-- Exact budget feasibility, simultaneously covering visible and invisible
responses, zero-dimensional spaces, and every real budget. -/
theorem finiteDimensional_dual_response_budget_iff (f : E →L[ℝ] ℝ) (r A : ℝ) :
    (∃ a : E, f a = r ∧ ‖a‖ ≤ A) ↔ 0 ≤ A ∧ |r| ≤ A * ‖f‖ := by
  constructor
  · rintro ⟨a, ha, hA⟩
    refine ⟨(norm_nonneg a).trans hA, ?_⟩
    have hbound := f.le_opNorm a
    rw [Real.norm_eq_abs, ha] at hbound
    simpa only [mul_comm] using
      hbound.trans (mul_le_mul_of_nonneg_left hA (norm_nonneg f))
  · rintro ⟨hA, hr⟩
    by_cases hf : 0 < ‖f‖
    · obtain ⟨a, ha, hn, _⟩ :=
        (finiteDimensional_dual_minimum_response_iff f r).mpr (Or.inr hf)
      exact ⟨a, ha, hn.le.trans ((div_le_iff₀ hf).mpr hr)⟩
    · have hf0 : ‖f‖ = 0 := le_antisymm (le_of_not_gt hf) (norm_nonneg f)
      have hr0 : r = 0 := by
        apply abs_eq_zero.mp
        exact le_antisymm (by simpa only [hf0, mul_zero] using hr) (abs_nonneg r)
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero, hr0]
      · simpa only [norm_zero] using hA

end RHTower
