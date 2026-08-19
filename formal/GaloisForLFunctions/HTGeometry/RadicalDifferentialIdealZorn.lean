import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealPrime

/-!
# A maximal non-finitely-generated radical differential ideal exists

The Zorn half of Ritt's basis theorem.  A chain of radical differential ideals has a radical
differential supremum, and that supremum is still not finitely generated: a finite generating set
would already lie in one member of the chain, which would then equal the supremum.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

omit [Differential R] in
/-- A finite subset of the supremum of a nonempty chain lies in one member. -/
theorem exists_mem_chain_of_finset_subset {c : Set (Ideal R)} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) :
    ∀ T : Finset R, (∀ t ∈ T, t ∈ sSup c) → ∃ J ∈ c, ∀ t ∈ T, t ∈ J := by
  classical
  intro T
  induction T using Finset.induction with
  | empty =>
      intro _
      obtain ⟨J, hJ⟩ := hne
      exact ⟨J, hJ, by simp⟩
  | insert a T ha ih =>
      intro hsub
      obtain ⟨J, hJc, hJ⟩ := ih fun t ht => hsub t (Finset.mem_insert_of_mem ht)
      have haS : a ∈ sSup c := hsub a (Finset.mem_insert_self a T)
      rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at haS
      obtain ⟨K, hKc, hKa⟩ := haS
      rcases eq_or_ne J K with rfl | hJK
      · exact ⟨J, hJc, by
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hKa
          · exact hJ t ht⟩
      · rcases hc hJc hKc hJK with hle | hle
        · exact ⟨K, hKc, by
            intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht
            · exact hKa
            · exact hle (hJ t ht)⟩
        · exact ⟨J, hJc, by
            intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht
            · exact hle hKa
            · exact hJ t ht⟩

/-- **Existence of a maximal non-finitely-generated radical differential ideal.** -/
theorem exists_maximal_not_radDiffFG
    (h : ∃ I : Ideal R, I.IsRadical ∧ (∀ x ∈ I, Differential.deriv x ∈ I) ∧ ¬ IsRadDiffFG I) :
    ∃ M : Ideal R, M.IsRadical ∧ (∀ x ∈ M, Differential.deriv x ∈ M) ∧ ¬ IsRadDiffFG M ∧
      ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → M < J →
        IsRadDiffFG J := by
  classical
  obtain ⟨I₀, hI₀rad, hI₀δ, hI₀fg⟩ := h
  set S : Set (Ideal R) :=
    {I : Ideal R | I.IsRadical ∧ (∀ x ∈ I, Differential.deriv x ∈ I) ∧ ¬ IsRadDiffFG I} with hS
  have hbound : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases Set.eq_empty_or_nonempty c with rfl | hne
    · exact ⟨I₀, ⟨hI₀rad, hI₀δ, hI₀fg⟩, by simp⟩
    refine ⟨sSup c, ⟨?_, ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro y hy
      obtain ⟨n, hn⟩ := hy
      rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hn ⊢
      obtain ⟨J, hJc, hJ⟩ := hn
      exact ⟨J, hJc, (hcS hJc).1 ⟨n, hJ⟩⟩
    · intro x hx
      rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
      obtain ⟨J, hJc, hJ⟩ := hx
      exact ⟨J, hJc, (hcS hJc).2.1 x hJ⟩
    · rintro ⟨T, hT⟩
      have hTsub : ∀ t ∈ T, t ∈ sSup c := by
        intro t ht
        rw [hT]
        exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
      obtain ⟨J, hJc, hJ⟩ := exists_mem_chain_of_finset_subset hc hne T hTsub
      have hJle : sSup c ≤ J := by
        rw [hT]
        exact radicalDifferentialIdeal_le (fun t ht => hJ t (by exact_mod_cast ht))
          (hcS hJc).1 (hcS hJc).2.1
      have hJeq : J = sSup c := le_antisymm (le_sSup hJc) hJle
      exact (hcS hJc).2.2 ⟨T, by rw [hJeq, hT]⟩
  obtain ⟨M, hM⟩ := zorn_le₀ S hbound
  refine ⟨M, hM.1.1, hM.1.2.1, hM.1.2.2, ?_⟩
  intro J hJrad hJδ hlt
  by_contra hJfg
  have hJS : J ∈ S := ⟨hJrad, hJδ, hJfg⟩
  exact absurd (hM.2 hJS (le_of_lt hlt)) (not_le_of_gt hlt)

end

end GaloisForLFunctions.HTGeometry
