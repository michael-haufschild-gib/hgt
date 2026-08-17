import GaloisForLFunctions.HTGeometry.NestedFoldedPhaseEvolution

/-!
# Finite phase-tail majorization
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {ι : Type*} [DecidableEq ι]

/-- If `K` contains at least as many elements as `N`, every weight outside `K` is at most a
threshold, and every weight inside `K` is at least it, then `K` has at least the weight of `N`. -/
theorem sum_le_sum_of_card_le_of_threshold
    (w : ι → ℝ) (K N : Finset ι) (m : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hcard : N.card ≤ K.card)
    (hout : ∀ e ∈ N \ K, w e ≤ m)
    (hin : ∀ e ∈ K \ N, m ≤ w e) :
    ∑ e ∈ N, w e ≤ ∑ e ∈ K, w e := by
  have hdiffCard : (N \ K).card ≤ (K \ N).card :=
    Finset.card_sdiff_le_card_sdiff_iff.mpr hcard
  have houtSum : ∑ e ∈ N \ K, w e ≤ (N \ K).card • m :=
    Finset.sum_le_card_nsmul _ _ _ hout
  have hinSum : (K \ N).card • m ≤ ∑ e ∈ K \ N, w e :=
    Finset.card_nsmul_le_sum _ _ _ hin
  have hdiff : ∑ e ∈ N \ K, w e ≤ ∑ e ∈ K \ N, w e := by
    by_cases hm : 0 ≤ m
    · have hsmul : (N \ K).card • m ≤ (K \ N).card • m :=
        nsmul_le_nsmul_left hm hdiffCard
      exact le_trans houtSum (le_trans hsmul hinSum)
    · have hzero : N \ K = ∅ := by
        ext e
        constructor
        · intro he
          exfalso
          have hout' := hout e he
          have hw' := hw e
          linarith
        · intro he
          simp at he
      rw [hzero]
      simp only [Finset.sum_empty, zero_le]
      exact Finset.sum_nonneg fun e he => hw e
  rw [← N.sum_inter_add_sum_sdiff K w, ← K.sum_inter_add_sum_sdiff N w]
  rw [Finset.inter_comm K N]
  linarith

/-- Removing no more edges than `K` removes no more total weight than `K`, hence leaves at least
the `K`-tail. -/
theorem tail_sum_le_of_threshold
    (E K N : Finset ι) (w : ι → ℝ) (m : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hK : K ⊆ E) (hN : N ⊆ E) (hcard : N.card ≤ K.card)
    (hout : ∀ e ∈ N \ K, w e ≤ m)
    (hin : ∀ e ∈ K \ N, m ≤ w e) :
    ∑ e ∈ E \ K, w e ≤ ∑ e ∈ E \ N, w e := by
  have hNK := sum_le_sum_of_card_le_of_threshold w K N m hw hcard hout hin
  have hEsplitK : ∑ e ∈ E \ K, w e + ∑ e ∈ K, w e = ∑ e ∈ E, w e :=
    Finset.sum_sdiff hK
  have hEsplitN : ∑ e ∈ E \ N, w e + ∑ e ∈ N, w e = ∑ e ∈ E, w e :=
    Finset.sum_sdiff hN
  linarith

/-- Global inside/outside threshold form of `tail_sum_le_of_threshold`. -/
theorem tail_sum_le_of_global_threshold
    (E K N : Finset ι) (w : ι → ℝ) (m : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hK : K ⊆ E) (hN : N ⊆ E) (hcard : N.card ≤ K.card)
    (hout : ∀ e ∈ E \ K, w e ≤ m)
    (hin : ∀ e ∈ K, m ≤ w e) :
    ∑ e ∈ E \ K, w e ≤ ∑ e ∈ E \ N, w e := by
  apply tail_sum_le_of_threshold E K N w m hw hK hN hcard
  · intro e he
    rcases Finset.mem_sdiff.mp he with ⟨heN, heK⟩
    exact hout e (Finset.mem_sdiff.mpr ⟨hN heN, heK⟩)
  · intro e he
    exact hin e (Finset.mem_sdiff.mp he).1

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
