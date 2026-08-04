import GaloisForLFunctions.RHTower.DeningerClassifyingSpace
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The fibre of a map of classifying spaces

The kernel square of a group homomorphism is a pullback of one object categories: a functor into the
source whose composite to the target is trivial factors uniquely through the kernel.  The nerve is a
right adjoint, so it carries that pullback to a pullback of simplicial sets: the classifying space of
the kernel is the fibre of the map of classifying spaces over the base point.

* `deningerPtKerCone`, `deningerPtKerCone_isLimit` : the kernel square is a pullback of categories.
* `deningerClassifyingFibre_isLimit` : its nerve is a pullback of simplicial sets, so the
  classifying space of the kernel is the fibre.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits SSet

universe u

variable {G H : Type u} [Group G] [Group H]

/-- The map of one object categories out of the kernel. -/
def deningerPtKerIncl (f : G →* H) : DeningerPt (f.ker) ⥤ DeningerPt G :=
  deningerPtMap f.ker.subtype

/-- The map of one object categories to the trivial group. -/
def deningerPtTrivial (K : Type u) [Group K] : DeningerPt K ⥤ DeningerPt PUnit.{u + 1} :=
  deningerPtMap (1 : K →* PUnit.{u + 1})

/-- **The lift of a cone into the kernel.** -/
def deningerPtKerLift (f : G →* H) {X : Type u} [Category.{u} X] (u : X ⥤ DeningerPt G)
    (h : ∀ {a b : X} (x : a ⟶ b), f (u.map x) = 1) : X ⥤ DeningerPt (f.ker) where
  obj _ := deningerPtStar (f.ker)
  map x := ⟨u.map x, h x⟩
  map_id a := Subtype.ext (by
    show (u.map (𝟙 a) : G) = 1
    rw [u.map_id]
    rfl)
  map_comp x y := Subtype.ext (by
    show (u.map (x ≫ y) : G) = _
    rw [u.map_comp]
    rfl)

/-- **The kernel square of a homomorphism**, as a square of one object categories. -/
def deningerPtKerCone (f : G →* H) :
    PullbackCone ((deningerPtMap f).toCatHom)
      ((deningerPtMap (1 : PUnit.{u + 1} →* H)).toCatHom) :=
  PullbackCone.mk (W := Cat.of (DeningerPt (f.ker)))
    ((deningerPtKerIncl f).toCatHom) ((deningerPtTrivial (f.ker)).toCatHom)
    (by
      refine Cat.Hom.ext (deningerPtHom_ext (fun {_ _} x => ?_))
      show f (Subtype.val x) = (1 : H)
      exact x.2)

/-- **The kernel square is a pullback of categories.** -/
def deningerPtKerCone_isLimit (f : G →* H) : IsLimit (deningerPtKerCone f) := by
  refine PullbackCone.isLimitAux' _ (fun s => ?_)
  have hcond : ∀ {a b : s.pt} (x : a ⟶ b), f (s.fst.toFunctor.map x) = 1 := by
    intro a b x
    have h := congrArg (fun g : (s.pt ⟶ Cat.of (DeningerPt H)) => g.toFunctor.map x) s.condition
    exact h
  refine ⟨(deningerPtKerLift f s.fst.toFunctor hcond).toCatHom, ?_, ?_, ?_⟩
  · exact Cat.Hom.ext (deningerPtHom_ext (fun {_ _} _ => rfl))
  · exact Cat.Hom.ext (deningerPtHom_ext (fun {_ _} _ =>
      Subsingleton.elim (α := PUnit.{u + 1}) _ _))
  · intro m hm _
    refine Cat.Hom.ext (deningerPtHom_ext (fun {_ _} x => ?_))
    have hx := congrArg (fun g : (s.pt ⟶ Cat.of (DeningerPt G)) => g.toFunctor.map x) hm
    refine Subtype.ext ?_
    show Subtype.val (m.toFunctor.map x) = s.fst.toFunctor.map x
    exact hx

/-- **The classifying space of the kernel is the fibre of the map of classifying spaces.**  The
nerve is a right adjoint, so it carries the kernel square to a pullback of simplicial sets. -/
noncomputable def deningerClassifyingFibre_isLimit (f : G →* H) :
    IsLimit (nerveFunctor.mapCone (deningerPtKerCone f)) :=
  haveI : Limits.PreservesLimit (cospan ((deningerPtMap f).toCatHom)
      ((deningerPtMap (1 : PUnit.{u + 1} →* H)).toCatHom)) nerveFunctor.{u, u} :=
    inferInstance
  isLimitOfPreserves _ (deningerPtKerCone_isLimit f)

end RHTower
