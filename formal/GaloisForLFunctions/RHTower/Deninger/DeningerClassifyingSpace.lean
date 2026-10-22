import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.SingleObj

/-!
# The classifying space of a group

The classifying space of a group is the nerve of its one object category, taken with the object in
the group's own universe so that the nerve adjunction applies.  The counit of that adjunction
identifies the homotopy category of the classifying space with the one object category again, so the
classifying space has one connected component and its fundamental group is the group itself.

* `DeningerPt`, `deningerPtToEnd` : the one object category of a group.
* `deningerClassifying`, `deningerClassifyingMap` : the classifying space and induced maps.
* `deningerClassifying_ho` : its homotopy category.
* `deningerClassifying_pi_one` : its fundamental group.
-/

namespace RHTower

open CategoryTheory SSet

universe u v w

/-- The one object category of a group. -/
structure DeningerPt (G : Type u) : Type u where
  /-- The unique object. -/
  mk ::

instance deningerPtCategory (G : Type u) [Group G] : Category.{u} (DeningerPt G) where
  Hom _ _ := G
  id _ := 1
  comp x y := y * x
  comp_id := one_mul
  id_comp := mul_one
  assoc f g h := (mul_assoc h g f).symm

/-- The unique object of the one object category. -/
def deningerPtStar (G : Type u) : DeningerPt G := DeningerPt.mk

/-- **The endomorphisms of the object are the group.** -/
def deningerPtToEnd (G : Type u) [Group G] : G ≃* End (deningerPtStar G) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **Two functors into a one object category agree** as soon as they agree on morphisms, the
objects being definitionally equal. -/
theorem deningerPtHom_ext {X : Type w} [Category.{v} X] {K : Type u} [Group K]
    {F G : X ⥤ DeningerPt K} (h : ∀ {a b : X} (x : a ⟶ b), F.map x = G.map x) : F = G :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun a b x => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact h x)

/-- The functor of one object categories induced by a homomorphism. -/
def deningerPtMap {G H : Type u} [Group G] [Group H] (f : G →* H) :
    DeningerPt G ⥤ DeningerPt H where
  obj _ := deningerPtStar H
  map x := f x
  map_id _ := f.map_one
  map_comp x y := f.map_mul y x

/-- **The classifying space of a group**: the nerve of its one object category. -/
abbrev deningerClassifying (G : Type u) [Group G] : SSet.{u} := nerve (DeningerPt G)

/-- **The map of classifying spaces induced by a homomorphism.** -/
def deningerClassifyingMap {G H : Type u} [Group G] [Group H] (f : G →* H) :
    deningerClassifying G ⟶ deningerClassifying H :=
  nerveFunctor.map (X := Cat.of (DeningerPt G)) (Y := Cat.of (DeningerPt H))
    (deningerPtMap f).toCatHom

/-- **The homotopy category of a classifying space is the one object category of the group.** -/
noncomputable def deningerClassifying_ho (G : Type u) [Group G] :
    SSet.hoFunctor.obj (deningerClassifying G) ≅ Cat.of (DeningerPt G) :=
  haveI : IsIso (nerveAdjunction.{u}).counit := nerveAdjunction.isIso_counit
  (asIso (nerveAdjunction.{u}).counit).app (Cat.of (DeningerPt G))

/-- **The fundamental group of a classifying space is the group**: the homotopy category has one
object, whose endomorphisms are the group. -/
noncomputable def deningerClassifying_pi_one (G : Type u) [Group G] :
    G ≃* End (((Cat.equivOfIso (deningerClassifying_ho G)).symm.functor).obj
      (deningerPtStar G)) :=
  (deningerPtToEnd G).trans
    ((Cat.equivOfIso (deningerClassifying_ho G)).symm.fullyFaithfulFunctor.mulEquivEnd
      (deningerPtStar G))

end RHTower
