import GaloisForLFunctions.HTGeometry.NerveHomotopy
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The link of a point in a building is the building of the quotient

The proper nonzero subspaces strictly above a fixed subspace correspond, under the submodule
correspondence theorem, to the proper nonzero subspaces of the quotient by it.

This is the induction engine of the Solomon--Tits argument: the link of a vertex of the building of
`V` is the building of a space of smaller dimension, so a statement about buildings can be proved by
induction on the dimension through the links.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Restricting an order isomorphism to matching subtypes. -/
def OrderIso.subtypeCongr {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    (P : α → Prop) (Q : β → Prop) (h : ∀ a, P a ↔ Q (e a)) :
    {a : α // P a} ≃o {b : β // Q b} where
  toFun a := ⟨e a.1, (h a.1).1 a.2⟩
  invFun b := ⟨e.symm b.1, (h (e.symm b.1)).2 (by rw [e.apply_symm_apply]; exact b.2)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.1)
  right_inv b := Subtype.ext (e.apply_symm_apply b.1)
  map_rel_iff' := e.map_rel_iff'

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **The link of a subspace is the building of the quotient.**  The proper subspaces strictly above
`p` are order isomorphic to the proper nonzero subspaces of `M ⧸ p`. -/
def linkQuotientOrderIso (p : Submodule R M) :
    {W : Submodule R (M ⧸ p) // ⊥ < W ∧ W < ⊤} ≃o {U : Submodule R M // p < U ∧ U < ⊤} := by
  classical
  refine (OrderIso.subtypeCongr (Submodule.comapMkQRelIso p)
    (fun W => ⊥ < W ∧ W < ⊤)
    (fun U : Set.Ici p => p < (U : Submodule R M) ∧ (U : Submodule R M) < ⊤) ?_).trans
    (OrderIso.subtypeCongr (OrderIso.refl (Set.Ici p)) _
      (fun U : Set.Ici p => p < (U : Submodule R M) ∧ (U : Submodule R M) < ⊤)
      (fun _ => Iff.rfl)) |>.trans ?_
  · intro W
    have hb : (Submodule.comapMkQRelIso p) ⊥ = ⟨p, Set.self_mem_Ici⟩ := OrderIso.map_bot _
    have ht : (Submodule.comapMkQRelIso p) ⊤ = ⟨⊤, Set.mem_Ici.2 le_top⟩ := OrderIso.map_top _
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have hlt := (Submodule.comapMkQRelIso p).lt_iff_lt.2 h1
        rw [hb] at hlt
        exact hlt
      · have hlt := (Submodule.comapMkQRelIso p).lt_iff_lt.2 h2
        rw [ht] at hlt
        exact hlt
    · rintro ⟨h1, h2⟩
      constructor
      · refine (Submodule.comapMkQRelIso p).lt_iff_lt.1 ?_
        rw [hb]
        exact h1
      · refine (Submodule.comapMkQRelIso p).lt_iff_lt.1 ?_
        rw [ht]
        exact h2
  · exact
      { toFun := fun U => ⟨(U.1 : Submodule R M), U.2⟩
        invFun := fun U => ⟨⟨U.1, le_of_lt U.2.1⟩, U.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }

end GaloisForLFunctions.HTGeometry
