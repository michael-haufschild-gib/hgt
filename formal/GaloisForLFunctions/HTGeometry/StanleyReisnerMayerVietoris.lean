import GaloisForLFunctions.HTGeometry.StanleyReisnerFacets

/-!
# The Mayer–Vietoris pair of a vertex

A complex is the union of the deletion and the star of any vertex, and their intersection is the
link.  On ideals, unions of face families become intersections and intersections become sums:

```text
faceStar F v                       the faces that stay faces after adding v
isFaceFamily_faceStar, isConePoint_faceStar    the star is a cone with apex v
faceDeletion_union_faceStar        del(v) ∪ st(v) = Δ
faceDeletion_inter_faceStar        del(v) ∩ st(v) = lk(v)
faceFamilyIdeal_union              I_{F ∪ G} = I_F ⊓ I_G
faceFamilyIdeal_inter              I_{F ∩ G} = I_F ⊔ I_G
faceFamilyIdeal_deletion_inf_star  ** I_Δ = I_{del(v)} ⊓ I_{st(v)} **
faceFamilyIdeal_link_eq_sup        ** I_{lk(v)} = I_{del(v)} ⊔ I_{st(v)} **
```

The sum identity is the one with content: split a polynomial by whether each monomial's support is a
face of `F`; the part that is not goes into `I_F`, and the part that is cannot be a face of `G`
either, so it goes into `I_G`.

These two identities are exactly the input of the Mayer–Vietoris short exact sequence

```text
0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0
```

on which the depth argument for the non-cone inductive step runs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- The star of a vertex: the faces that stay faces after adding it. -/
def faceStar (F : Finset (Finset σ)) (v : σ) : Finset (Finset σ) :=
  F.filter (fun S => insert v S ∈ F)

omit [Fintype σ] in
theorem mem_faceStar {F : Finset (Finset σ)} {v : σ} {S : Finset σ} :
    S ∈ faceStar F v ↔ S ∈ F ∧ insert v S ∈ F := by
  simp [faceStar]

omit [Fintype σ] in
theorem isFaceFamily_faceStar {F : Finset (Finset σ)} (hF : IsFaceFamily F) (v : σ) :
    IsFaceFamily (faceStar F v) := by
  intro S T hT hST
  rw [mem_faceStar] at hT ⊢
  exact ⟨hF hT.1 hST, hF hT.2 (Finset.insert_subset_insert v hST)⟩

omit [Fintype σ] in
theorem faceDeletion_union_faceStar {F : Finset (Finset σ)} (v : σ) :
    faceDeletion F v ∪ faceStar F v = F := by
  classical
  ext S
  simp only [Finset.mem_union, mem_faceDeletion, mem_faceStar]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro hS
    by_cases hv : v ∈ S
    · exact Or.inr ⟨hS, by rwa [Finset.insert_eq_self.mpr hv]⟩
    · exact Or.inl ⟨hS, hv⟩

omit [Fintype σ] in
theorem faceDeletion_inter_faceStar {F : Finset (Finset σ)} (v : σ) :
    faceDeletion F v ∩ faceStar F v = faceLink F v := by
  classical
  ext S
  simp only [Finset.mem_inter, mem_faceDeletion, mem_faceStar, mem_faceLink]
  constructor
  · rintro ⟨⟨hS, hv⟩, -, hins⟩
    exact ⟨hS, hv, hins⟩
  · rintro ⟨hS, hv, hins⟩
    exact ⟨⟨hS, hv⟩, hS, hins⟩

/-- **The ideal of a union of face families is the intersection of the ideals.** -/
theorem faceFamilyIdeal_union (K : Type u) [Field K] (F G : Finset (Finset σ))
    (hF : IsFaceFamily F) (hG : IsFaceFamily G) :
    faceFamilyIdeal K (F ∪ G) = faceFamilyIdeal K F ⊓ faceFamilyIdeal K G := by
  classical
  have hFG : IsFaceFamily (F ∪ G) := by
    intro S T hT hST
    rw [Finset.mem_union] at hT ⊢
    rcases hT with h | h
    · exact Or.inl (hF h hST)
    · exact Or.inr (hG h hST)
  ext p
  rw [mem_faceFamilyIdeal_iff hFG, Submodule.mem_inf, mem_faceFamilyIdeal_iff hF,
    mem_faceFamilyIdeal_iff hG]
  constructor
  · intro h
    exact ⟨fun e he hmem => h e he (Finset.mem_union_left _ hmem),
      fun e he hmem => h e he (Finset.mem_union_right _ hmem)⟩
  · rintro ⟨h1, h2⟩ e he hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact h1 e he h
    · exact h2 e he h

/-- **The ideal of an intersection of face families is the sum of the ideals.** -/
theorem faceFamilyIdeal_inter (K : Type u) [Field K] (F G : Finset (Finset σ))
    (hF : IsFaceFamily F) (hG : IsFaceFamily G) :
    faceFamilyIdeal K (F ∩ G) = faceFamilyIdeal K F ⊔ faceFamilyIdeal K G := by
  classical
  have hFG : IsFaceFamily (F ∩ G) := by
    intro S T hT hST
    rw [Finset.mem_inter] at hT ⊢
    exact ⟨hF hT.1 hST, hG hT.2 hST⟩
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro p hp
    rw [mem_faceFamilyIdeal_iff hFG] at hp
    have hsplit : ∑ e ∈ p.support.filter (fun e => e.support ∉ F),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)
        + ∑ e ∈ p.support.filter (fun e => ¬ (e.support ∉ F)),
          MvPolynomial.monomial e (MvPolynomial.coeff e p) = p := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact MvPolynomial.support_sum_monomial_coeff p
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, hsplit⟩
    · refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [mem_faceFamilyIdeal_iff hF]
      intro f hf
      have hfe : f = e := by
        have := MvPolynomial.support_monomial_subset (a := MvPolynomial.coeff e p) (s := e) hf
        simpa using this
      subst hfe
      exact he.2
    · refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter, not_not] at he
      rw [mem_faceFamilyIdeal_iff hG]
      intro f hf
      have hfe : f = e := by
        have := MvPolynomial.support_monomial_subset (a := MvPolynomial.coeff e p) (s := e) hf
        simpa using this
      subst hfe
      intro hmemG
      exact hp f he.1 (Finset.mem_inter.mpr ⟨he.2, hmemG⟩)
  · rw [faceFamilyIdeal, faceFamilyIdeal]
    exact Finset.inf_mono Finset.inter_subset_left
  · rw [faceFamilyIdeal, faceFamilyIdeal]
    exact Finset.inf_mono Finset.inter_subset_right

/-- **The Mayer–Vietoris pair of a vertex.**  The Stanley–Reisner ideal is the intersection of those
of the deletion and the star, and the ideal of the link is their sum. -/
theorem faceFamilyIdeal_deletion_inf_star (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    faceFamilyIdeal K F
      = faceFamilyIdeal K (faceDeletion F v) ⊓ faceFamilyIdeal K (faceStar F v) := by
  rw [← faceFamilyIdeal_union K _ _ (isFaceFamily_faceDeletion hF v) (isFaceFamily_faceStar hF v),
    faceDeletion_union_faceStar v]

theorem faceFamilyIdeal_link_eq_sup (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    faceFamilyIdeal K (faceLink F v)
      = faceFamilyIdeal K (faceDeletion F v) ⊔ faceFamilyIdeal K (faceStar F v) := by
  rw [← faceDeletion_inter_faceStar v,
    faceFamilyIdeal_inter K _ _ (isFaceFamily_faceDeletion hF v) (isFaceFamily_faceStar hF v)]

omit [Fintype σ] in
/-- The star is a cone with apex the vertex. -/
theorem isConePoint_faceStar {F : Finset (Finset σ)} (v : σ) :
    IsConePoint (faceStar F v) v := by
  classical
  intro S hS
  rw [mem_faceStar] at hS ⊢
  refine ⟨hS.2, ?_⟩
  rw [Finset.insert_idem]
  exact hS.2


end GaloisForLFunctions.HTGeometry
