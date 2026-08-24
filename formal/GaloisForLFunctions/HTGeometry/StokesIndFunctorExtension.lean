import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Covariant functor extension to ind-categories

Every functor `F : C ⥤ D`, with `D` finitely cocomplete, extends covariantly to ind-categories by
pointwise left Kan extension of `F ⋙ Ind.yoneda` along `Ind.yoneda`. The comparison is an
isomorphism on representables.

No preservation theorem for finite limits, finite colimits, or filtered colimits is asserted here.
-/

namespace CategoryTheory

open Limits Functor

universe v u

namespace Ind

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable [HasFiniteColimits D]

/-- Pointwise left Kan extension along Yoneda exists because its comma categories are filtered and
finally small, while the target ind-category has small colimits. -/
noncomputable instance yonedaHasPointwiseLeftKanExtension (F : C ⥤ Ind D) :
    (Ind.yoneda : C ⥤ Ind C).HasPointwiseLeftKanExtension F := fun X => by
  let e : CostructuredArrow (Ind.yoneda : C ⥤ Ind C) X ≌
      CostructuredArrow yoneda ((Ind.inclusion C).obj X) :=
    (CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)
  letI : FinallySmall.{v} (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) :=
    (Ind.isIndObject_inclusion_obj X).finallySmall
  letI : FinallySmall.{v} (CostructuredArrow (Ind.yoneda : C ⥤ Ind C) X) :=
    finallySmall_of_final_of_finallySmall e.inverse
  letI : HasColimitsOfShape
      (CostructuredArrow (Ind.yoneda : C ⥤ Ind C) X) (Ind D) :=
    hasColimitsOfShape_of_finallySmall _ _
  infer_instance

/-- Covariant extension of a functor to ind-categories. -/
noncomputable def map (F : C ⥤ D) : Ind C ⥤ Ind D :=
  (Ind.yoneda : C ⥤ Ind C).pointwiseLeftKanExtension (F ⋙ Ind.yoneda)

/-- Pointwise Kan-extension comparison on representables. -/
noncomputable def mapYonedaHom (F : C ⥤ D) :
    F ⋙ Ind.yoneda ⟶ Ind.yoneda ⋙ Ind.map F :=
  (Ind.yoneda : C ⥤ Ind C).pointwiseLeftKanExtensionUnit (F ⋙ Ind.yoneda)

noncomputable instance mapYonedaHom_app_isIso (F : C ⥤ D) (X : C) :
    IsIso ((Ind.mapYonedaHom F).app X) :=
  (((Ind.yoneda : C ⥤ Ind C).pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (F ⋙ Ind.yoneda)) ((Ind.yoneda : C ⥤ Ind C).obj X)).isIso_hom_app

noncomputable instance mapYonedaHom_isIso (F : C ⥤ D) :
    IsIso (Ind.mapYonedaHom F) :=
  NatIso.isIso_of_isIso_app _

/-- Ind-extension agrees with the original functor on representables. -/
noncomputable def mapYonedaIso (F : C ⥤ D) :
    F ⋙ Ind.yoneda ≅ Ind.yoneda ⋙ Ind.map F :=
  asIso (Ind.mapYonedaHom F)

end Ind

end CategoryTheory
