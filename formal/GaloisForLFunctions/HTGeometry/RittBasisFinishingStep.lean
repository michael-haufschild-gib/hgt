import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealSaturation

/-!
# The finishing step of Ritt's basis theorem

A maximal non-finitely-generated radical differential ideal cannot admit a finite subset `N` and an
element `h` outside it such that some power of `h` pushes every element into the radical
differential ideal of `N`.  Maximality makes `{M, h}` finitely generated, finite exhaustion replaces
its generators by a finite subset of `M` together with `h`, and the saturation decomposition then
collapses `M` onto the radical differential ideal of a finite set.

This is the abstract form of the last step of Ritt's basis theorem: the reduction algorithm supplies
`N` (the derivatives of a minimal-rank element) and `h` (the initial times the separant).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- **The finishing step.** -/
theorem isRadDiffFG_of_saturation {M : Ideal R} (hrad : M.IsRadical)
    (hδ : ∀ x ∈ M, Differential.deriv x ∈ M)
    (hmax : ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → M < J →
      IsRadDiffFG J)
    {h : R} (hh : h ∉ M) {N : Finset R} (hN : ↑N ⊆ (M : Set R))
    (hsat : ∀ Q ∈ M, ∃ j : ℕ, h ^ j * Q ∈ radicalDifferentialIdeal (N : Set R)) :
    IsRadDiffFG M := by
  classical
  set A := radicalDifferentialIdeal ((M : Set R) ∪ {h}) with hA
  have hMA : M ≤ A := fun x hx => subset_radicalDifferentialIdeal _ (Or.inl hx)
  have hhA : h ∈ A := subset_radicalDifferentialIdeal _ (Or.inr rfl)
  have hlt : M < A := lt_of_le_of_ne hMA fun heq => hh (heq ▸ hhA)
  obtain ⟨T, hT⟩ := hmax A (isRadical_radicalDifferentialIdeal _)
    (deriv_mem_radicalDifferentialIdeal _) hlt
  have hchoice : ∀ t ∈ T, ∃ St : Finset R, ↑St ⊆ ((M : Set R) ∪ {h}) ∧
      t ∈ radicalDifferentialIdeal (St : Set R) := by
    intro t ht
    refine exists_finset_subset_mem_radicalDifferentialIdeal (S := (M : Set R) ∪ {h}) ?_
    rw [← hA, hT]
    exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
  choose! St hSt1 hSt2 using hchoice
  set S : Finset R := T.biUnion St with hS
  have hSsub : ↑S ⊆ ((M : Set R) ∪ {h}) := by
    intro y hy
    obtain ⟨t, ht, hyt⟩ := Finset.mem_biUnion.mp (by exact_mod_cast hy)
    exact hSt1 t ht (by exact_mod_cast hyt)
  have hAS : A = radicalDifferentialIdeal (S : Set R) := by
    refine le_antisymm ?_ (radicalDifferentialIdeal_le
      (fun y hy => subset_radicalDifferentialIdeal _ (hSsub hy))
      (isRadical_radicalDifferentialIdeal _) (deriv_mem_radicalDifferentialIdeal _))
    rw [hT]
    refine radicalDifferentialIdeal_le ?_ (isRadical_radicalDifferentialIdeal _)
      (deriv_mem_radicalDifferentialIdeal _)
    intro t ht
    have htT : t ∈ T := by exact_mod_cast ht
    refine radicalDifferentialIdeal_mono ?_ (hSt2 t htT)
    intro y hy
    exact_mod_cast Finset.mem_biUnion.mpr ⟨t, htT, by exact_mod_cast hy⟩
  set S₀ : Finset R := S.erase h with hS₀
  have hS₀M : ↑S₀ ⊆ (M : Set R) := by
    intro y hy
    have hy' : y ∈ S.erase h := by exact_mod_cast hy
    rcases hSsub (by exact_mod_cast Finset.mem_of_mem_erase hy') with hm | hm
    · exact hm
    · exact absurd (by rw [← Set.mem_singleton_iff.mp hm]) (Finset.ne_of_mem_erase hy')
  set N' : Finset R := N ∪ S₀ with hN'
  have hN'M : ↑N' ⊆ (M : Set R) := by
    intro y hy
    rcases Finset.mem_union.mp (by exact_mod_cast hy) with hm | hm
    · exact hN (by exact_mod_cast hm)
    · exact hS₀M (by exact_mod_cast hm)
  set J : Ideal R := radicalDifferentialIdeal (N' : Set R) with hJ
  have hJM : J ≤ M := radicalDifferentialIdeal_le hN'M hrad hδ
  have hMJ : M ≤ J := by
    intro Q hQ
    refine mem_of_saturation_of_mem_adjoin (h := h) (isRadical_radicalDifferentialIdeal _)
      (deriv_mem_radicalDifferentialIdeal _) ?_ ?_
    · obtain ⟨j, hj⟩ := hsat Q hQ
      refine ⟨j, radicalDifferentialIdeal_mono ?_ hj⟩
      intro y hy
      exact_mod_cast Finset.mem_union_left S₀ (by exact_mod_cast hy)
    · have hQA : Q ∈ A := hMA hQ
      rw [hAS] at hQA
      refine radicalDifferentialIdeal_le (S := (S : Set R))
        (I := radicalDifferentialIdeal ((J : Set R) ∪ {h})) ?_
        (isRadical_radicalDifferentialIdeal _) (deriv_mem_radicalDifferentialIdeal _) hQA
      intro y hy
      by_cases hyh : y = h
      · exact subset_radicalDifferentialIdeal _ (Or.inr (by rw [hyh]; rfl))
      · refine subset_radicalDifferentialIdeal _ (Or.inl ?_)
        have hy0 : y ∈ S₀ := Finset.mem_erase.mpr ⟨hyh, by exact_mod_cast hy⟩
        exact subset_radicalDifferentialIdeal _
          (by exact_mod_cast Finset.mem_union_right N hy0)
  exact ⟨N', le_antisymm hMJ hJM⟩

end

end GaloisForLFunctions.HTGeometry
