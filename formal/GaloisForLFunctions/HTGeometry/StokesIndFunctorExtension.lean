import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Covariant functor extension to ind-categories

Every functor `F : C ⥤ D` extends covariantly to ind-categories by left Kan extension of presheaves
along `Fᵒᵖ`. The Kan extension of a filtered colimit of representables is again a filtered colimit
of representables, so it restricts to ind-objects. The comparison is an isomorphism on
representables.

No preservation theorem for finite limits, finite colimits, or filtered colimits is asserted here.
-/

namespace CategoryTheory

open Limits Functor

universe v u

namespace Ind

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Left Kan extension sends Yoneda representables to Yoneda representables. -/
noncomputable def yonedaCompLanIso (F : C ⥤ D) :
    yoneda ⋙ F.op.lan ≅ F ⋙ yoneda :=
  isoWhiskerRight uliftYonedaIsoYoneda.symm F.op.lan ≪≫
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm ≪≫
    isoWhiskerLeft F uliftYonedaIsoYoneda

/-- Applying presheaf left Kan extension to a presentation replaces every representing object by
its image under `F`. -/
noncomputable def lanPresentationDiagramIso (F : C ⥤ D)
    {A : Cᵒᵖ ⥤ Type u} (P : IndObjectPresentation A) :
    (P.F ⋙ yoneda) ⋙ F.op.lan ≅ (P.F ⋙ F) ⋙ yoneda :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft P.F (yonedaCompLanIso F) ≪≫
    (Functor.associator _ _ _).symm

/-- Presheaf left Kan extension carries a chosen filtered presentation to the corresponding
filtered presentation of the image. -/
noncomputable def lanObjIsoPresentationColimit (F : C ⥤ D)
    {A : Cᵒᵖ ⥤ Type u} (P : IndObjectPresentation A) :
    F.op.lan.obj A ≅ colimit ((P.F ⋙ F) ⋙ yoneda) := by
  letI : PreservesColimits (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) :=
    (F.op.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  exact F.op.lan.mapIso
      (IsColimit.coconePointUniqueUpToIso P.coconeIsColimit
        (colimit.isColimit (P.F ⋙ yoneda))) ≪≫
    preservesColimitIso F.op.lan (P.F ⋙ yoneda) ≪≫
    HasColimit.isoOfNatIso (lanPresentationDiagramIso F P)

/-- Left Kan extension of an ind-object is an ind-object. -/
theorem lan_obj_isIndObject (F : C ⥤ D) {A : Cᵒᵖ ⥤ Type u}
    (hA : IsIndObject A) : IsIndObject (F.op.lan.obj A) := by
  let P := hA.presentation
  let e := lanObjIsoPresentationColimit F P
  exact IsIndObject.mk (.ofCocone
    ((colimit.cocone ((P.F ⋙ F) ⋙ yoneda)).extend e.inv)
    ((colimit.isColimit ((P.F ⋙ F) ⋙ yoneda)).extendIso e.inv))

/-- Presheaf left Kan extension lifted to the full subcategory of ind-objects. -/
noncomputable def mapLift (F : C ⥤ D) :
    Ind C ⥤ ObjectProperty.FullSubcategory (IsIndObject (C := D)) :=
  ObjectProperty.lift _ (Ind.inclusion C ⋙ F.op.lan)
    (fun X => lan_obj_isIndObject F (Ind.isIndObject_inclusion_obj X))

/-- Covariant extension of a functor to ind-categories. -/
noncomputable def map (F : C ⥤ D) : Ind C ⥤ Ind D :=
  mapLift F ⋙ (Ind.equivalence D).inverse

/-- Underlying presheaf of the ind-extension is presheaf left Kan extension. -/
noncomputable def mapCompInclusionIso (F : C ⥤ D) :
    Ind.map F ⋙ Ind.inclusion D ≅ Ind.inclusion C ⋙ F.op.lan :=
  isoWhiskerLeft (mapLift F)
    (isoWhiskerRight (Ind.equivalence D).counitIso (ObjectProperty.ι _))

private noncomputable def mapYonedaCompInclusionIso (F : C ⥤ D) :
    (F ⋙ Ind.yoneda) ⋙ Ind.inclusion D ≅
      (Ind.yoneda ⋙ Ind.map F) ⋙ Ind.inclusion D :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F Ind.yonedaCompInclusion ≪≫
    (yonedaCompLanIso F).symm ≪≫
    isoWhiskerRight Ind.yonedaCompInclusion.symm F.op.lan ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Ind.yoneda (mapCompInclusionIso F).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Ind-extension agrees with the original functor on representables. -/
noncomputable def mapYonedaIso (F : C ⥤ D) :
    F ⋙ Ind.yoneda ≅ Ind.yoneda ⋙ Ind.map F :=
  (Ind.inclusion.fullyFaithful (C := D)).whiskeringRight C |>.preimageIso
    (mapYonedaCompInclusionIso F)

/-- Hom of the comparison between the original functor and its ind-extension on representables. -/
noncomputable def mapYonedaHom (F : C ⥤ D) :
    F ⋙ Ind.yoneda ⟶ Ind.yoneda ⋙ Ind.map F :=
  (mapYonedaIso F).hom

noncomputable instance mapYonedaHom_app_isIso (F : C ⥤ D) (X : C) :
    IsIso ((Ind.mapYonedaHom F).app X) := by
  dsimp only [mapYonedaHom]
  infer_instance

noncomputable instance mapYonedaHom_isIso (F : C ⥤ D) :
    IsIso (Ind.mapYonedaHom F) := by
  dsimp only [mapYonedaHom]
  infer_instance

end Ind

end CategoryTheory
