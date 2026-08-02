import GaloisForLFunctions.HTGeometry.ApartmentInterval
import GaloisForLFunctions.HTGeometry.ApartmentClassMono

/-!
# An apartment meets the cover of the building in its own cover

The Solomon--Tits cover of the building is a base of non-spanning subspaces together with the stars
of the spanning coatoms.  Inside the apartment of a frame that contains the chosen line, spanning is
a purely combinatorial condition: a coordinate subspace spans with that line exactly when its
coordinate set is the complement of the line's index.  So the cover of the building cuts the
apartment along its own cover, and a chamber of the apartment lies wholly in the base or wholly in
the single star.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite Module

universe u

section

variable {K V ι : Type u} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The coordinate subspace of a union is the join of the coordinate subspaces. -/
theorem coordSpan_union (b : Basis ι K V) (s t : Set ι) :
    coordSpan b (s ∪ t) = coordSpan b s ⊔ coordSpan b t := by
  rw [coordSpan, coordSpan, coordSpan, Set.image_union, Submodule.span_union]

/-- **Inside an apartment, spanning with a frame line is combinatorial.** -/
theorem coordSpan_sup_singleton_eq_top_iff (b : Basis ι K V) (a : ι) (s : Set ι) :
    coordSpan b s ⊔ coordSpan b {a} = ⊤ ↔ s ∪ {a} = Set.univ := by
  rw [← coordSpan_union]
  constructor
  · intro h
    refine coordSpan_injective b ?_
    rw [h, coordSpan_univ]
  · intro h
    rw [h, coordSpan_univ]

/-- **A vertex of an apartment that is not the coatom opposite a frame vector does not span with
it.**  So a chamber of the apartment missing that coatom lies wholly in the base of the cover. -/
theorem coordSpan_sup_singleton_ne_top (b : Basis ι K V) {a : ι} (U : properPart (Set ι))
    (h : (U : Set ι) ≠ Set.univ \ {a}) :
    coordSpan b (U : Set ι) ⊔ coordSpan b {a} ≠ ⊤ := by
  intro hcon
  exact apartment_not_spanning_of_ne U h
    ((coordSpan_sup_singleton_eq_top_iff b a (U : Set ι)).1 hcon)

/-- **And the coatom opposite a frame vector does span with it.** -/
theorem coordSpan_compl_sup_singleton (b : Basis ι K V) (a : ι) :
    coordSpan b (Set.univ \ {a}) ⊔ coordSpan b {a} = ⊤ := by
  rw [coordSpan_sup_singleton_eq_top_iff]
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x = a
  · exact Or.inr (Set.mem_singleton_iff.2 hx)
  · exact Or.inl ⟨Set.mem_univ x, fun hcon => hx (Set.mem_singleton_iff.1 hcon)⟩

/-- **A vertex of an apartment other than the coatom is a vertex of the base of the cover.** -/
theorem apartmentVertices_mem_notSpanning (b : Basis ι K V) {a : ι} (U : properPart (Set ι))
    (h : (U : Set ι) ≠ Set.univ \ {a}) :
    apartmentVertices b U ∈ notSpanning (coordSpan b {a}) :=
  coordSpan_sup_singleton_ne_top b U h

/-- **The coatom opposite a frame vector is a vertex of the star of the cover.** -/
theorem apartmentVertices_mem_spanning (b : Basis ι K V) (a : ι)
    (hbot : (⊥ : Set ι) < Set.univ \ {a}) (htop : (Set.univ \ {a} : Set ι) < ⊤) :
    apartmentVertices b ⟨Set.univ \ {a}, hbot, htop⟩ ∈ spanning (coordSpan b {a}) :=
  coordSpan_compl_sup_singleton b a

end

/-! ## Chambers of an apartment lie wholly in the base or wholly in the star -/

section Chambers

variable {K V ι : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [Finite ι]

omit [Finite ι] in
/-- Every vertex of a chamber is contained in its top vertex. -/
theorem chainOfOrdering_le_last {n : ℕ} (e : Fin (n + 2) ≃ ι) (i : Fin (n + 1)) :
    ((chainOfOrdering e i : properPart (Set ι)) : Set ι)
      ⊆ ((chainOfOrdering e (Fin.last n) : properPart (Set ι)) : Set ι) :=
  (chainOfOrdering_strictMono e).monotone (Fin.le_last i)

/-- **A chamber whose ordering does not end with the chosen vector misses the coatom entirely.** -/
theorem chainOfOrdering_ne_compl {n : ℕ} (hN : Nat.card ι = n + 2) (e : Fin (n + 2) ≃ ι) {a : ι}
    (hne : e (Fin.last (n + 1)) ≠ a) (i : Fin (n + 1)) :
    ((chainOfOrdering e i : properPart (Set ι)) : Set ι) ≠ Set.univ \ {a} := fun hcon =>
  hne ((chainOfOrdering_eq_compl_singleton_iff hN e a i).1 hcon).2

/-- **Then all its vertices are vertices of the base of the cover.** -/
theorem chamber_mem_notSpanning {n : ℕ} (hN : Nat.card ι = n + 2) (b : Basis ι K V)
    (e : Fin (n + 2) ≃ ι) {a : ι} (hne : e (Fin.last (n + 1)) ≠ a) (i : Fin (n + 1)) :
    apartmentVertices b (chainOfOrdering e i) ∈ notSpanning (coordSpan b {a}) :=
  apartmentVertices_mem_notSpanning b _ (chainOfOrdering_ne_compl hN e hne i)

/-- **And if it does end with the chosen vector, all its vertices lie in the star of the coatom.** -/
theorem chamber_mem_generalStar {n : ℕ} (hN : Nat.card ι = n + 2) (b : Basis ι K V)
    (e : Fin (n + 2) ≃ ι) {a : ι} (he : e (Fin.last (n + 1)) = a) (i : Fin (n + 1))
    (hbot : (⊥ : Set ι) < Set.univ \ {a}) (htop : (Set.univ \ {a} : Set ι) < ⊤) :
    apartmentVertices b (chainOfOrdering e i)
      ∈ generalStar (apartmentVertices b ⟨Set.univ \ {a}, hbot, htop⟩) := by
  refine Or.inl ((apartmentVertices b).monotone ?_)
  have hlast : ((chainOfOrdering e (Fin.last n) : properPart (Set ι)) : Set ι) = Set.univ \ {a} :=
    (chainOfOrdering_eq_compl_singleton_iff hN e a (Fin.last n)).2 ⟨by simp, he⟩
  show ((chainOfOrdering e i : properPart (Set ι)) : Set ι) ⊆ (Set.univ \ {a} : Set ι)
  rw [← hlast]
  exact chainOfOrdering_le_last e i

end Chambers

/-! ## The apartment inside the disjoint-union presentation of the building -/

section FamBuilding

variable {K V ι : Type u} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The apartment of a frame, as a subposet of the disjoint-union presentation of the building that
the Mayer--Vietoris cover is stated on. -/
def apartmentToFamBuilding (b : Basis ι K V) :
    properPart (Set ι) →o famBuilding (fun _ : PUnit.{u + 1} => (⊤ : Submodule K V)) where
  toFun U := ⟨(PUnit.unit, apartmentVertices b U), (apartmentVertices b U).2.2⟩
  monotone' _ _ h := ⟨rfl, (apartmentVertices b).monotone h⟩

/-- **A vertex of an apartment other than the coatom is a vertex of the base of the cover**, in the
presentation the descent uses. -/
theorem apartmentToFamBuilding_mem_famCoverBase (b : Basis ι K V) {a : ι}
    (U : properPart (Set ι)) (h : (U : Set ι) ≠ Set.univ \ {a}) :
    apartmentToFamBuilding b U
      ∈ famCoverBase (fun _ : PUnit.{u + 1} => (⊤ : Submodule K V))
        (fun _ => coordSpan b {a}) := by
  refine ⟨?_, ?_⟩
  · exact (apartmentVertices b U).2.2
  · exact coordSpan_sup_singleton_ne_top b U h

/-- **And the vertices below the coatom lie in the star of the cover.** -/
theorem apartmentToFamBuilding_mem_generalStar (b : Basis ι K V) {a : ι}
    (U : properPart (Set ι)) (hbot : (⊥ : Set ι) < Set.univ \ {a})
    (htop : (Set.univ \ {a} : Set ι) < ⊤) (hle : (U : Set ι) ⊆ Set.univ \ {a}) :
    apartmentToFamBuilding b U
      ∈ generalStar (apartmentToFamBuilding b ⟨Set.univ \ {a}, hbot, htop⟩) := by
  exact Or.inl ⟨rfl, (apartmentVertices b).monotone hle⟩

end FamBuilding

end GaloisForLFunctions.HTGeometry
