import GaloisForLFunctions.HTGeometry.StokesFreePresheafTensorFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Tensor-flat projective module presheaves

The canonical free module presheaf on the underlying type-valued presheaf surjects onto every
module presheaf. For a projective target this presentation splits, so every component is a retract
of a free module and is flat. Pointwise flatness then makes tensor exact and degreewise tensor
preserves quasi-isomorphisms.

This proves the degree-zero projective-cell case only. It does not construct K-flat complexes or
derived tensor products.
-/

open CategoryTheory Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.ProjectivePresheafTensorFlat

open FreePresheafTensorFlat

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Module presheaves over the underlying ring presheaf of `A`. -/
abbrev ModulePresheaf :=
  PresheafOfModules.{u} (underlyingRingPresheaf A)

/-- Underlying type-valued presheaf of a module presheaf. -/
noncomputable abbrev underlyingTypePresheaf (P : ModulePresheaf A) : Cᵒᵖ ⥤ Type u :=
  P.presheaf ⋙ forget _

/-- Canonical free presentation obtained from the free-forgetful adjunction. -/
noncomputable def freePresentation (P : ModulePresheaf A) :
    freeModulePresheaf A (underlyingTypePresheaf A P) ⟶ P :=
  PresheafOfModules.freeObjDesc (𝟙 _)

/-- The canonical free presentation is pointwise surjective, hence epic. -/
noncomputable instance freePresentationEpi (P : ModulePresheaf A) :
    Epi (freePresentation A P) :=
  PresheafOfModules.epi_of_surjective (fun {X} p =>
    ⟨ModuleCat.freeMk p, by
      exact ModuleCat.freeDesc_apply (𝟙 _) p⟩)

/-- A chosen section of the canonical free presentation of a projective module presheaf. -/
noncomputable def projectiveSection (P : ModulePresheaf A) [Projective P] :
    P ⟶ freeModulePresheaf A (underlyingTypePresheaf A P) :=
  Projective.factorThru (𝟙 P) (freePresentation A P)

@[reassoc (attr := simp)]
theorem projectiveSection_comp (P : ModulePresheaf A) [Projective P] :
    projectiveSection A P ≫ freePresentation A P = 𝟙 P :=
  Projective.factorThru_comp (𝟙 P) (freePresentation A P)

/-- Every component of a projective module presheaf is a flat module. -/
noncomputable instance projectivePointwiseFlat (P : ModulePresheaf A) [Projective P]
    (X : Cᵒᵖ) : Module.Flat (A.obj X) (P.obj X) := by
  letI : Module.Flat ((underlyingRingPresheaf A).obj X)
      ((freeModulePresheaf A (underlyingTypePresheaf A P)).obj X) :=
    freeModulePresheafPointwiseFlat A (underlyingTypePresheaf A P) X
  apply Module.Flat.of_retract
    ((projectiveSection A P).app X).hom
    ((freePresentation A P).app X).hom
  ext p
  have h := congrArg (fun f => f.app X) (projectiveSection_comp A P)
  exact ConcreteCategory.congr_hom h p

/-- Pointwise flatness implies that left tensor preserves finite limits. -/
theorem tensorLeftPreservesFiniteLimitsOfPointwiseFlat
    (P : ModulePresheaf A) (hP : ∀ X : Cᵒᵖ, Module.Flat (A.obj X) (P.obj X)) :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft P) where
  preservesFiniteLimits J _ _ := ⟨fun {K} => ⟨fun {c} hc => ⟨
    PresheafOfModules.evaluationJointlyReflectsLimits
      (R := underlyingRingPresheaf A)
      (K ⋙ MonoidalCategory.tensorLeft P)
      ((MonoidalCategory.tensorLeft P).mapCone c) (fun X => by
        letI : Module.Flat ((underlyingRingPresheaf A).obj X) (P.obj X) := hP X
        exact isLimitOfPreserves
          (MonoidalCategory.tensorLeft (show ModuleCat (A.obj X) from P.obj X))
          (isLimitOfPreserves
            (PresheafOfModules.evaluation (underlyingRingPresheaf A) X) hc))⟩⟩⟩

/-- Tensoring on the left by a projective module presheaf preserves finite limits. -/
noncomputable instance projectiveTensorLeftPreservesFiniteLimits
    (P : ModulePresheaf A) [Projective P] :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft P) :=
  tensorLeftPreservesFiniteLimitsOfPointwiseFlat A P (fun X =>
    projectivePointwiseFlat A P X)

/-- Tensoring on the right by a projective module presheaf preserves finite limits. -/
noncomputable instance projectiveTensorRightPreservesFiniteLimits
    (P : ModulePresheaf A) [Projective P] :
    PreservesFiniteLimits (MonoidalCategory.tensorRight P) :=
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight P)

/-- Degreewise left tensor by a projective module presheaf maps quasi-isomorphisms of nonnegative
chain complexes to quasi-isomorphisms. -/
theorem projectiveTensorLeft_map_quasiIso
    (P : ModulePresheaf A) [Projective P]
    {K L : ChainComplex (PresheafComplexTensor.ModulePresheaf A) ℕ}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso
      (((MonoidalCategory.tensorLeft P).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) := by
  exact HomologicalComplex.quasiIso_map_of_preservesHomology φ _

/-- Degreewise right tensor by a projective module presheaf maps quasi-isomorphisms of nonnegative
chain complexes to quasi-isomorphisms. -/
theorem projectiveTensorRight_map_quasiIso
    (P : ModulePresheaf A) [Projective P]
    {K L : ChainComplex (PresheafComplexTensor.ModulePresheaf A) ℕ}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso
      (((MonoidalCategory.tensorRight P).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) := by
  exact HomologicalComplex.quasiIso_map_of_preservesHomology φ _

end GaloisForLFunctions.IrregularStokes.ProjectivePresheafTensorFlat
