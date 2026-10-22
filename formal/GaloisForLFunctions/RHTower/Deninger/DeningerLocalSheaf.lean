import GaloisForLFunctions.RHTower.Deninger.DeningerFineSurjective

/-!
# Sheaves of abelian groups cut out by a local condition on functions

A local predicate on functions with values in a fixed abelian group, closed under the group
operations, cuts out a sheaf of abelian groups: the sections over an open set are the functions
satisfying the predicate there, and the sheaf condition is the one for the underlying sheaf of
types, which is the mathlib construction for a local predicate.

This is the shape every sheaf of the Dolbeault resolution has: holomorphic functions, smooth
functions, and smooth forms are all functions satisfying a condition that can be checked near each
point and is preserved by addition.

* `RHTower.DeningerLocalGroupData` : the data of such a predicate.
* `RHTower.DeningerLocalGroupData.sheaf` : the resulting sheaf of abelian groups.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- A local predicate on functions into an abelian group, closed under the group operations. -/
structure DeningerLocalGroupData (X : TopCat.{u}) (V : Type u) [AddCommGroup V] where
  /-- The local predicate cutting out the sections. -/
  toLocalPredicate : TopCat.LocalPredicate (fun _ : (X : Type u) => V)
  pred_zero : ∀ U : Opens X, toLocalPredicate.pred (U := U) (fun _ => 0)
  pred_add : ∀ (U : Opens X) (f g : ↥U → V), toLocalPredicate.pred (U := U) f →
    toLocalPredicate.pred (U := U) g → toLocalPredicate.pred (U := U) (fun x => f x + g x)
  pred_neg : ∀ (U : Opens X) (f : ↥U → V), toLocalPredicate.pred (U := U) f →
    toLocalPredicate.pred (U := U) (fun x => -f x)

namespace DeningerLocalGroupData

variable {V : Type u} [AddCommGroup V] (D : DeningerLocalGroupData X V)

/-- The sections over an open set, as a subgroup of all functions. -/
def subgroup (U : Opens X) : AddSubgroup (↥U → V) where
  carrier := {f | D.toLocalPredicate.pred (U := U) f}
  zero_mem' := D.pred_zero U
  add_mem' := fun {a b} ha hb => D.pred_add U a b ha hb
  neg_mem' := fun {a} ha => D.pred_neg U a ha

/-- The presheaf of functions satisfying the predicate. -/
def presheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of ↥(D.subgroup (unop U))
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun x => f.1 (i.unop x), D.toLocalPredicate.res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of types is the mathlib presheaf attached to the local predicate. -/
def forgetIso :
    TopCat.subpresheafToTypes D.toLocalPredicate.toPrelocalPredicate ≅
      D.presheaf ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

theorem presheaf_isSheaf : D.presheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u})]
  exact TopCat.Presheaf.isSheaf_of_iso D.forgetIso
    (TopCat.subpresheafToTypes.isSheaf D.toLocalPredicate)

/-- **The sheaf of abelian groups cut out by a local predicate.** -/
def sheaf : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨D.presheaf, D.presheaf_isSheaf⟩

@[simp] theorem sheaf_obj (U : Opens X) :
    ToType ((D.sheaf).1.obj (op U)) = ↥(D.subgroup U) := rfl

@[simp] theorem sheaf_res_apply {U W : Opens X} (h : W ≤ U) (f : ToType (D.sheaf.1.obj (op U)))
    (x : ↥W) : (deningerRes D.sheaf h f).1 x = f.1 ⟨x.1, h x.2⟩ := rfl

/-- Two sections agree when their underlying functions do. -/
theorem sheaf_ext {U : Opens X} {f g : ToType (D.sheaf.1.obj (op U))}
    (h : ∀ x : ↥U, f.1 x = g.1 x) : f = g :=
  Subtype.ext (funext h)

end DeningerLocalGroupData

end RHTower
