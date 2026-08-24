import GaloisForLFunctions.HTGeometry.StokesDerivedEpigraphDirectImage
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Projective resolutions and degreewise derived tensor for module presheaves

This file supplies the projective-resolution layer available below a future derived
tensor product for enhanced sheaves.  It deliberately works with presheaves of modules:
general sheaf categories need not have enough projectives.

Mathlib currently exposes projective-resolution left-derived functors one homology
degree at a time.  Accordingly, the final definitions here are families indexed by
`n : ℕ`; they are not derived-category tensor bifunctors.
-/

open CategoryTheory Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.PresheafDerivedTensor

variable {C : Type u} [SmallCategory C]

/-- A free Yoneda module presheaf is projective: its morphisms represent evaluation,
and epimorphisms of module presheaves are pointwise surjective. -/
noncomputable instance freeYonedaProjective
    (R : Cᵒᵖ ⥤ RingCat.{u}) (X : C) :
    Projective ((PresheafOfModules.free R).obj (yoneda.obj X)) where
  factors := by
    intro E M f e _
    let x : M.obj (Opposite.op X) := PresheafOfModules.freeYonedaEquiv f
    haveI : Epi (e.app (Opposite.op X)) := inferInstance
    obtain ⟨y, hy⟩ :=
      (ModuleCat.epi_iff_surjective (e.app (Opposite.op X))).mp inferInstance x
    refine ⟨PresheafOfModules.freeYonedaEquiv.symm y, ?_⟩
    apply PresheafOfModules.freeYonedaEquiv.injective
    rw [PresheafOfModules.freeYonedaEquiv_comp]
    simpa [x] using hy

/-- Presheaves of modules over a ring presheaf on a small category have enough
projectives, supplied by coproducts of free Yoneda module presheaves. -/
noncomputable instance enoughProjectives (R : Cᵒᵖ ⥤ RingCat.{u}) :
    EnoughProjectives (PresheafOfModules.{u} R) where
  presentation M := ⟨{
    p := M.freeYonedaCoproduct
    projective := inferInstance
    f := M.fromFreeYonedaCoproduct
    epi := inferInstance
  }⟩

/-- The preceding projective presentations generate projective resolutions. -/
theorem hasProjectiveResolutions (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasProjectiveResolutions (PresheafOfModules.{u} R) :=
  inferInstance

variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Tensoring on the left by a fixed module presheaf is additive. -/
noncomputable instance tensorLeftAdditive
    (G : PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat))) :
    (MonoidalCategory.tensorLeft G).Additive :=
  let F := MonoidalCategory.tensorLeft G
  letI : F.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  Functor.additive_of_preservesBinaryBiproducts F

/-- Tensoring on the right by a fixed module presheaf is additive. -/
noncomputable instance tensorRightAdditive
    (G : PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat))) :
    (MonoidalCategory.tensorRight G).Additive :=
  let F := MonoidalCategory.tensorRight G
  letI : F.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  Functor.additive_of_preservesBinaryBiproducts F

/-- Degree-`n` left-derived functor of `G ⊗ -` on module presheaves. -/
noncomputable def leftDerivedTensorLeft
    (G : PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat))) (n : ℕ) :
    PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat)) :=
  (MonoidalCategory.tensorLeft G).leftDerived n

/-- Degree-`n` left-derived functor of `- ⊗ G` on module presheaves. -/
noncomputable def leftDerivedTensorRight
    (G : PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat))) (n : ℕ) :
    PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat)) ⥤
      PresheafOfModules.{u} (A.comp (forget₂ CommRingCat RingCat)) :=
  (MonoidalCategory.tensorRight G).leftDerived n

end GaloisForLFunctions.IrregularStokes.PresheafDerivedTensor
