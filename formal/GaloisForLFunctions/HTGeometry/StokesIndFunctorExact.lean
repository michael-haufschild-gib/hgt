import GaloisForLFunctions.HTGeometry.StokesIndFunctorExtension
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Exact covariant extension to ind-categories

If `F : C ⥤ D` preserves finite limits, its presheaf left Kan extension and hence `Ind.map F`
preserve finite limits. If `F` preserves finite colimits, precomposition along `Fᵒᵖ` restricts to
ind-objects; the restricted Kan-extension adjunction then makes `Ind.map F` a left adjoint, so it
preserves finite colimits.
-/

namespace CategoryTheory

open Limits Functor

universe u

namespace Ind


variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- An ind-extension of a finite-limit-preserving functor preserves finite limits. -/
noncomputable instance map_preservesFiniteLimits (F : C ⥤ D)
    [HasFiniteLimits C] [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Ind.map F) := by
  haveI : PreservesFiniteLimits (Ind.inclusion C) := inferInstance
  haveI : PreservesFiniteLimits
      (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) := inferInstance
  haveI : PreservesFiniteLimits (Ind.inclusion C ⋙ F.op.lan) :=
    comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteLimits (Ind.map F ⋙ Ind.inclusion D) :=
    preservesFiniteLimits_of_natIso (mapCompInclusionIso F).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Ind.inclusion D)

/-- Precomposition of presheaves along `Fᵒᵖ`. -/
noncomputable def precomposePresheaf (F : C ⥤ D) :
    (Dᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u :=
  (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op

/-- If `F` preserves finite colimits, precomposition along `Fᵒᵖ` sends ind-objects to
ind-objects. -/
theorem precompose_isIndObject (F : C ⥤ D) [HasFiniteColimits C]
    [HasFiniteColimits D] [PreservesFiniteColimits F] (X : Ind D) :
    IsIndObject (F.op ⋙ (Ind.inclusion D).obj X) := by
  rw [isIndObject_iff_preservesFiniteLimits]
  letI : PreservesFiniteLimits ((Ind.inclusion D).obj X) :=
    (isIndObject_iff_preservesFiniteLimits _).mp (Ind.isIndObject_inclusion_obj X)
  haveI : PreservesFiniteLimits F.op := preservesFiniteLimits_op F
  exact comp_preservesFiniteLimits _ _

/-- Presheaf precomposition lifted to the full subcategory of ind-objects. -/
noncomputable def preLift (F : C ⥤ D) [HasFiniteColimits C]
    [HasFiniteColimits D] [PreservesFiniteColimits F] :
    Ind D ⥤ ObjectProperty.FullSubcategory (IsIndObject (C := C)) :=
  ObjectProperty.lift _ (Ind.inclusion D ⋙ precomposePresheaf F)
    (precompose_isIndObject F)

/-- Right adjoint candidate for covariant ind-extension: precomposition along `Fᵒᵖ`. -/
noncomputable def pre (F : C ⥤ D) [HasFiniteColimits C]
    [HasFiniteColimits D] [PreservesFiniteColimits F] : Ind D ⥤ Ind C :=
  preLift F ⋙ (Ind.equivalence C).inverse

/-- Underlying presheaf of `Ind.pre F` is precomposition along `Fᵒᵖ`. -/
noncomputable def preCompInclusionIso (F : C ⥤ D) [HasFiniteColimits C]
    [HasFiniteColimits D] [PreservesFiniteColimits F] :
    pre F ⋙ Ind.inclusion C ≅ Ind.inclusion D ⋙ precomposePresheaf F :=
  isoWhiskerLeft (preLift F)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))

/-- Restricted presheaf Kan-extension adjunction on ind-categories. -/
noncomputable def mapAdjunction (F : C ⥤ D) [HasFiniteColimits C]
    [HasFiniteColimits D] [PreservesFiniteColimits F] : Ind.map F ⊣ pre F :=
  (F.op.lanAdjunction (Type u)).restrictFullyFaithful
    (Ind.inclusion.fullyFaithful (C := C)) (Ind.inclusion.fullyFaithful (C := D))
    (mapCompInclusionIso F).symm (preCompInclusionIso F).symm

/-- An ind-extension of a finite-colimit-preserving functor preserves finite colimits. -/
noncomputable instance map_preservesFiniteColimits (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (Ind.map F) := by
  letI : PreservesColimits (Ind.map F) :=
    (mapAdjunction F).leftAdjoint_preservesColimits
  infer_instance

/-- Unit components of the restricted Kan adjunction are isomorphisms when `F` is fully
faithful. -/
noncomputable instance mapAdjunction_unit_app_isIso (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] (X : Ind C) :
    IsIso ((mapAdjunction F).unit.app X) := by
  letI : IsIso ((Ind.inclusion C).map ((mapAdjunction F).unit.app X)) := by
    dsimp only [mapAdjunction]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    have h₁ : IsIso
        ((F.op.lanAdjunction (Type u)).unit.app ((Ind.inclusion C).obj X)) := by
      infer_instance
    have h₂ : IsIso (((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op).map
        ((mapCompInclusionIso F).symm.hom.app X)) := by
      infer_instance
    have h₃ : IsIso ((preCompInclusionIso F).symm.hom.app ((map F).obj X)) := by
      infer_instance
    exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)
  exact isIso_of_reflects_iso _ (Ind.inclusion C)

noncomputable instance mapAdjunction_unit_isIso (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] : IsIso (mapAdjunction F).unit :=
  NatIso.isIso_of_isIso_app _

/-- Covariant ind-extension preserves full faithfulness. -/
noncomputable def mapFullyFaithful (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] : (Ind.map F).FullyFaithful :=
  (mapAdjunction F).fullyFaithfulLOfIsIsoUnit

noncomputable instance map_full (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] : (Ind.map F).Full :=
  (mapFullyFaithful F).full

instance map_faithful (F : C ⥤ D)
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] : (Ind.map F).Faithful :=
  (mapFullyFaithful F).faithful

end Ind

end CategoryTheory
