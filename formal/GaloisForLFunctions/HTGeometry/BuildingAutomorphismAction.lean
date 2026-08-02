import GaloisForLFunctions.HTGeometry.BuildingVanishingSubmodule
import Mathlib.Algebra.Order.Group.End

/-!
# The automorphisms of a lattice act on the homology of its building

An order isomorphism of bounded lattices restricts to the proper parts, hence induces an isomorphism
of order complexes and of their homology in every degree.  The construction is functorial, so the
automorphism group of the lattice acts on each homology object.

For the subspaces of a vector space this is the action of the linear group on the homology of the
Tits building: in the top degree, the Steinberg representation.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

variable {L L' L'' : Type u} [Lattice L] [BoundedOrder L] [Lattice L'] [BoundedOrder L']
  [Lattice L''] [BoundedOrder L'']

/-- **An order isomorphism restricts to the proper parts.** -/
def properPartCongr (e : L ≃o L') : properPart L ≃o properPart L' where
  toFun x :=
    ⟨e x, by rw [← e.map_bot]; exact e.strictMono x.2.1,
      by rw [← e.map_top]; exact e.strictMono x.2.2⟩
  invFun y :=
    ⟨e.symm y, by rw [← e.symm.map_bot]; exact e.symm.strictMono y.2.1,
      by rw [← e.symm.map_top]; exact e.symm.strictMono y.2.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : L))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : L'))
  map_rel_iff' {a b} := e.map_rel_iff

@[simp] theorem properPartCongr_apply (e : L ≃o L') (x : properPart L) :
    ((properPartCongr e x : properPart L') : L') = e (x : L) := rfl

theorem properPartCongr_refl :
    properPartCongr (OrderIso.refl L) = OrderIso.refl (properPart L) := by
  refine OrderIso.ext (funext (fun x => ?_))
  exact Subtype.ext rfl

theorem properPartCongr_trans (e : L ≃o L') (e' : L' ≃o L'') :
    properPartCongr (e.trans e') = (properPartCongr e).trans (properPartCongr e') := by
  refine OrderIso.ext (funext (fun x => ?_))
  exact Subtype.ext rfl

/-- **Order-isomorphic lattices have isomorphic order complexes of proper parts.** -/
noncomputable def properPartNerveIso (e : L ≃o L') :
    nerveFunctor.obj (Cat.of (properPart L)) ≅ nerveFunctor.obj (Cat.of (properPart L')) :=
  orderIsoNerveIso (properPartCongr e)

theorem orderIsoCatIso_refl :
    orderIsoCatIso (OrderIso.refl (properPart L)) = Iso.refl (Cat.of (properPart L)) := by
  refine Iso.ext (Cat.ext ?_)
  show Monotone.functor (OrderIso.refl (properPart L)).monotone
    = CategoryTheory.Functor.id (properPart L)
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

theorem orderIsoCatIso_trans (e : properPart L ≃o properPart L')
    (e' : properPart L' ≃o properPart L'') :
    orderIsoCatIso (e.trans e') = orderIsoCatIso e ≪≫ orderIsoCatIso e' := by
  refine Iso.ext (Cat.ext ?_)
  show Monotone.functor (e.trans e').monotone
    = (Monotone.functor e.monotone).comp (Monotone.functor e'.monotone)
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

section

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- **The automorphism group of a bounded lattice acts on the homology of its building.** -/
noncomputable def buildingHomologyAut (R : C) (i : ℕ) :
    (L ≃o L) →* Aut ((nerveFunctor.obj (Cat.of (properPart L))).homology R i) where
  toFun e := (SSet.homologyFunctor R i).mapIso (properPartNerveIso e)
  map_one' := by
    show (SSet.homologyFunctor R i).mapIso (properPartNerveIso (OrderIso.refl L)) = Iso.refl _
    rw [properPartNerveIso, orderIsoNerveIso, properPartCongr_refl, orderIsoCatIso_refl,
      nerveFunctor.mapIso_refl, CategoryTheory.Functor.mapIso_refl]
  map_mul' e f := by
    show (SSet.homologyFunctor R i).mapIso (properPartNerveIso (f.trans e))
      = (SSet.homologyFunctor R i).mapIso (properPartNerveIso f)
        ≪≫ (SSet.homologyFunctor R i).mapIso (properPartNerveIso e)
    rw [properPartNerveIso, properPartNerveIso, properPartNerveIso, orderIsoNerveIso,
      orderIsoNerveIso, orderIsoNerveIso, properPartCongr_trans, orderIsoCatIso_trans,
      nerveFunctor.mapIso_trans, CategoryTheory.Functor.mapIso_trans]

end

section Steinberg

variable (K V : Type u) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **A linear automorphism as an order automorphism of the subspace lattice.** -/
def submoduleAutHom : (V ≃ₗ[K] V) →* (Submodule K V ≃o Submodule K V) where
  toFun f := Submodule.orderIsoMapComap f
  map_one' := by
    refine OrderIso.ext (funext (fun U => ?_))
    refine SetLike.ext (fun x => ?_)
    simp [Submodule.orderIsoMapComap]
  map_mul' f g := by
    refine OrderIso.ext (funext (fun U => ?_))
    refine SetLike.ext (fun x => ?_)
    simp [Submodule.orderIsoMapComap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨g.symm (f.symm x), h, by simp⟩

variable [FiniteDimensional K V]

section

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- **The Steinberg module**: the homology of the building of a vector space in its top degree. -/
noncomputable def steinbergModule (R : C) : C :=
  (nerveFunctor.obj (Cat.of (properPart (Submodule K V)))).homology R (finrank K V - 2)

/-- **The linear group acts on the Steinberg module.**  This is the Steinberg representation of the
projective observer group on the top homology of the horizon complex. -/
noncomputable def steinbergAction (R : C) : (V ≃ₗ[K] V) →* Aut (steinbergModule K V R) :=
  (buildingHomologyAut R (finrank K V - 2)).comp (submoduleAutHom K V)

end

end Steinberg

end GaloisForLFunctions.HTGeometry
