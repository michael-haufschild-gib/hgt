import GaloisForLFunctions.HTGeometry.NerveMayerVietoris

/-!
# Removing any vertex from an order complex

The star of an arbitrary element of a poset — the elements comparable to it — is contractible, and
together with the full subcomplex on the complement of that element it covers the order complex: a
chain either contains the element, and then all of its members are comparable to it, or it avoids it.

So an order complex can be cut at *any* vertex, not only a minimal one, and the homology of the whole
is controlled by the complement and by the punctured star.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u

variable {P : Type u} [PartialOrder P]

/-- The star of an element: everything comparable to it. -/
def generalStar (p : P) : Set P := {q : P | q ≤ p ∨ p ≤ q}

open scoped Classical in
/-- Folding the star onto its centre. -/
noncomputable def generalStarCone (p : P) : (generalStar p : Type u) →o (generalStar p : Type u) where
  toFun q := if (q : P) ≤ p then ⟨p, Or.inl le_rfl⟩ else q
  monotone' q q' h := by
    by_cases hq : (q : P) ≤ p
    · by_cases hq' : (q' : P) ≤ p
      · simp only [if_pos hq, if_pos hq']
        exact le_rfl
      · simp only [if_pos hq, if_neg hq']
        exact q'.2.resolve_left hq'
    · have hq' : ¬ (q' : P) ≤ p := fun hcon => hq (le_trans h hcon)
      simp only [if_neg hq, if_neg hq']
      exact h

/-- **The star of any element is contractible.** -/
theorem isZero_homology_generalStar (p : P) {C : Type u} [Category.{v} C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (i : ℕ)
    (hi : 1 ≤ i) :
    Limits.IsZero (((nerveSubcomplex (generalStar p) : SSet.{u})).homology R i) := by
  classical
  refine Limits.IsZero.of_iso ?_ (nerveSubcomplexHomologyIso _ R i)
  refine isZero_homology_of_conical (⟨p, Or.inl le_rfl⟩ : (generalStar p : Type u))
    (generalStarCone p) (fun q => ?_) (fun q => ?_) R i hi
  · change (q : P) ≤ ((generalStarCone p) q : P)
    simp only [generalStarCone, OrderHom.coe_mk]
    split_ifs with hq
    · exact hq
    · exact le_rfl
  · change p ≤ ((generalStarCone p) q : P)
    simp only [generalStarCone, OrderHom.coe_mk]
    split_ifs with hq
    · exact le_rfl
    · exact q.2.resolve_left hq

/-- **The star of any element and the complement of that element cover the order complex.** -/
theorem nerveSubcomplex_generalStar_sup_compl (p : P) :
    nerveSubcomplex (generalStar p) ⊔ nerveSubcomplex {q : P | q ≠ p} = ⊤ := by
  refine nerveSubcomplex_sup_eq_top (fun U x => ?_)
  by_cases hx : ∃ i, x.obj i = p
  · obtain ⟨i, hi⟩ := hx
    refine Or.inl (fun j => ?_)
    rcases le_total j i with hij | hij
    · exact Or.inl (hi ▸ leOfHom (x.map (homOfLE hij)))
    · exact Or.inr (hi ▸ leOfHom (x.map (homOfLE hij)))
  · exact Or.inr (fun j hj => hx ⟨j, hj⟩)

/-- **Cutting an order complex at an arbitrary vertex.** -/
theorem isZero_homology_nerve_of_vertex (p : P)
    {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hcompl : Limits.IsZero (((nerveSubcomplex {q : P | q ≠ p} : SSet.{u})).homology R i))
    (hlink : Limits.IsZero
      (((nerveSubcomplex (generalStar p ∩ {q : P | q ≠ p}) : SSet.{u})).homology R j)) :
    Limits.IsZero (((nerve P).chainComplex R).homology i) := by
  refine isZero_homology_of_mayerVietoris (nerve P) R (nerveSubcomplex (generalStar p))
    (nerveSubcomplex {q : P | q ≠ p}) (nerveSubcomplex_generalStar_sup_compl p) i j hij
    (isZero_homology_generalStar p R i hi) hcompl ?_
  rw [← nerveSubcomplex_inter]
  exact hlink

end GaloisForLFunctions.HTGeometry
