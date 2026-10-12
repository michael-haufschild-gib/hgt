import GaloisForLFunctions.HTGeometry.IntermediateAffinityReplication
import GaloisForLFunctions.HTGeometry.FastAffinityReplication

/-! The complete limit spectrum of escaping powers of affinities bounded by one. -/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem exists_ennreal_powers_tendsto_iff {f : ℕ → ℝ≥0∞} {c q : ℝ≥0∞}
    (hbound : ∀ r, f r ≤ 1) (hf : Tendsto f atTop (𝓝 c)) :
    (∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      Tendsto (fun r => f r ^ m r) atTop (𝓝 q)) ↔
      (c < 1 ∧ q = 0) ∨
        (c = 1 ∧ (q = 1 ∨ (q < 1 ∧ ∀ᶠ r in atTop, f r < 1))) := by
  have hc : c ≤ 1 := le_of_tendsto' hf hbound
  constructor
  · rintro ⟨m, hm, hq⟩
    rcases lt_or_eq_of_le hc with hc | hc
    · exact Or.inl ⟨hc, tendsto_nhds_unique hq
        (tendsto_ennreal_powers_zero_of_tendsto_lt_one hf hc hm)⟩
    · refine Or.inr ⟨hc, ?_⟩
      by_cases hq1 : q = 1
      · exact Or.inl hq1
      · have hlt : q < 1 := lt_of_le_of_ne
          (le_of_tendsto' hq (fun r => pow_le_one' (hbound r) (m r))) hq1
        refine Or.inr ⟨hlt, ?_⟩
        filter_upwards [hq.eventually (gt_mem_nhds hlt)] with r hr
        by_contra h
        have hpow : 1 ≤ f r ^ m r := one_le_pow₀ (le_of_not_gt h)
        exact not_lt_of_ge hpow hr
  · rintro (⟨hc, rfl⟩ | ⟨hc, htarget⟩)
    · exact ⟨id, tendsto_id,
        tendsto_ennreal_powers_zero_of_tendsto_lt_one hf hc tendsto_id⟩
    · rw [hc] at hf
      rcases htarget with rfl | ⟨hq1, hstrict⟩
      · obtain ⟨m, _, _, hm, hpow⟩ := exists_monotone_ennreal_powers_tendsto_one hf
        exact ⟨m, hm, hpow⟩
      · by_cases hq0 : q = 0
        · subst q
          obtain ⟨m, _, _, hm, hpow⟩ :=
            (exists_monotone_ennreal_fast_powers_zero_iff f).mpr hstrict
          exact ⟨m, hm, hpow⟩
        · exact exists_ennreal_powers_tendsto_intermediate hf hstrict
            (lt_of_le_of_ne bot_le (Ne.symm hq0)) hq1

end GaloisForLFunctions.HTGeometry
