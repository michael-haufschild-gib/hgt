import GaloisForLFunctions.HTGeometry.BuildingNotSpanning

/-!
# The homology of the link is the homology of the quotient building

Transporting the link identification along the nerve: the order complex of the proper subspaces
strictly above `p` has the same homology as the order complex of the building of `M ⧸ p`.

This is the induction step of a dimension induction on buildings, in the form a homology argument
consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

/-- An isomorphism of simplicial sets induces an isomorphism on homology. -/
noncomputable def homologyIsoOfIso {X Y : SSet.{u}} (e : X ≅ Y) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) :
    X.homology R n ≅ Y.homology R n where
  hom := SSet.homologyMap e.hom R n
  inv := SSet.homologyMap e.inv R n
  hom_inv_id := by
    rw [← SSet.homologyMap_comp, e.hom_inv_id, SSet.homologyMap_id]
  inv_hom_id := by
    rw [← SSet.homologyMap_comp, e.inv_hom_id, SSet.homologyMap_id]

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- **The link of a subspace has the homology of the building of the quotient.** -/
noncomputable def linkHomologyIso (p : Submodule R M) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (Rc : C) (n : ℕ) :
    (nerveFunctor.obj (Cat.of {U : Submodule R M // p < U ∧ U < ⊤})).homology Rc n
      ≅ (nerveFunctor.obj
        (Cat.of {W : Submodule R (M ⧸ p) // ⊥ < W ∧ W < ⊤})).homology Rc n :=
  homologyIsoOfIso (orderIsoNerveIso (linkQuotientOrderIso p).symm) Rc n

end GaloisForLFunctions.HTGeometry
