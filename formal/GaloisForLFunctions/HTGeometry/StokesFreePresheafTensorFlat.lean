import GaloisForLFunctions.HTGeometry.StokesPresheafComplexTensor
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Tensor-flat free module presheaves

Free module presheaves are pointwise free, hence flat. Tensoring by one therefore preserves finite
limits and homology, so its degreewise action on chain complexes preserves quasi-isomorphisms.

This is the degree-zero free-cell seed of a future K-flat construction, not a proof that arbitrary
projective complexes are K-flat.
-/

open CategoryTheory Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.FreePresheafTensorFlat

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u}) (F : Cᵒᵖ ⥤ Type u)

/-- Underlying presheaf of rings. -/
abbrev underlyingRingPresheaf : Cᵒᵖ ⥤ RingCat.{u} :=
  A.comp (forget₂ CommRingCat RingCat)

/-- Pointwise free module presheaf on a type-valued presheaf. -/
noncomputable abbrev freeModulePresheaf :
    PresheafOfModules.{u} (underlyingRingPresheaf A) :=
  (PresheafOfModules.free (underlyingRingPresheaf A)).obj F

/-- Every component of a free module presheaf is a flat module. -/
noncomputable instance freeModulePresheafPointwiseFlat (X : Cᵒᵖ) :
    Module.Flat (A.obj X) ((freeModulePresheaf A F).obj X) := by
  dsimp [freeModulePresheaf, underlyingRingPresheaf,
    PresheafOfModules.free, PresheafOfModules.freeObj]
  change Module.Flat (A.obj X) (F.obj X →₀ A.obj X)
  infer_instance

/-- Tensoring on the left by a free module presheaf preserves finite limits. The proof checks
flatness after every evaluation and uses joint reflection of presheaf limits. -/
noncomputable instance freeTensorLeftPreservesFiniteLimits :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft (freeModulePresheaf A F)) where
  preservesFiniteLimits J _ _ := ⟨fun {K} => ⟨fun {c} hc => ⟨
    PresheafOfModules.evaluationJointlyReflectsLimits
      (R := underlyingRingPresheaf A)
      (K ⋙ MonoidalCategory.tensorLeft (freeModulePresheaf A F))
      ((MonoidalCategory.tensorLeft (freeModulePresheaf A F)).mapCone c) (fun X => by
        exact isLimitOfPreserves
          (MonoidalCategory.tensorLeft
            (show ModuleCat (A.obj X) from (freeModulePresheaf A F).obj X))
          (isLimitOfPreserves
            (PresheafOfModules.evaluation (underlyingRingPresheaf A) X) hc))⟩⟩⟩

/-- Tensoring on the right by a free module presheaf preserves finite limits by symmetry. -/
noncomputable instance freeTensorRightPreservesFiniteLimits :
    PreservesFiniteLimits (MonoidalCategory.tensorRight (freeModulePresheaf A F)) :=
  preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight (freeModulePresheaf A F))

/-- Degreewise left tensor by a free module presheaf maps quasi-isomorphisms of nonnegative
chain complexes to quasi-isomorphisms. -/
theorem freeTensorLeft_map_quasiIso
    {K L : ChainComplex (PresheafComplexTensor.ModulePresheaf A) ℕ}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso
      (((MonoidalCategory.tensorLeft (freeModulePresheaf A F)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) := by
  exact HomologicalComplex.quasiIso_map_of_preservesHomology φ _

/-- Degreewise right tensor by a free module presheaf maps quasi-isomorphisms of nonnegative
chain complexes to quasi-isomorphisms. -/
theorem freeTensorRight_map_quasiIso
    {K L : ChainComplex (PresheafComplexTensor.ModulePresheaf A) ℕ}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso
      (((MonoidalCategory.tensorRight (freeModulePresheaf A F)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) := by
  exact HomologicalComplex.quasiIso_map_of_preservesHomology φ _

end GaloisForLFunctions.IrregularStokes.FreePresheafTensorFlat
