import GaloisForLFunctions.HTGeometry.StokesProjectiveComplexTensorKFlat
import Mathlib.Algebra.Homology.Localization

/-!
# Derived tensor by a componentwise-projective complex

For nonnegative module-presheaf complexes, total left tensor by a componentwise-projective
complex preserves quasi-isomorphisms. The universal property of localization therefore descends
this chain-level functor to the category localized at quasi-isomorphisms.

This is fixed-representative infrastructure. It does not assert existence of projective or K-flat
resolutions for arbitrary complexes.
-/

open CategoryTheory Limits MonoidalCategory

universe w u

namespace GaloisForLFunctions.IrregularStokes.ProjectiveDerivedTensor

open ProjectiveComplexTensorKFlat

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

abbrev M := PresheafComplexTensor.ModulePresheaf A
abbrev CC := ChainComplex (M A) ℕ
abbrev W := HomologicalComplex.quasiIso (M A) (ComplexShape.down ℕ)

variable [MorphismProperty.HasLocalization.{w} (W A)]

/-- Nonnegative module-presheaf complexes localized at quasi-isomorphisms. -/
abbrev DerivedCC := HomologicalComplexUpToQuasiIso (M A) (ComplexShape.down ℕ)

/-- Chain-level total left tensor by `P`. -/
noncomputable def tensorLeftFunctor (P : CC A) : CC A ⥤ CC A := by
  letI : MonoidalCategory (CC A) :=
    PresheafComplexTensor.chainComplexMonoidalCategory A
  exact MonoidalCategory.tensorLeft P

omit [MorphismProperty.HasLocalization.{w} (W A)] in
/-- Chain-level total left tensor by a componentwise-projective complex preserves
quasi-isomorphisms. -/
theorem tensorLeftFunctor_map_quasiIso
    (P : CC A) [∀ n, Projective (P.X n)] {X Y : CC A}
    (φ : X ⟶ Y) [QuasiIso φ] :
    QuasiIso ((tensorLeftFunctor A P).map φ) := by
  exact componentwiseProjectiveTotalTensorLeft_map_quasiIso A P φ

/-- Composing total left tensor by a componentwise-projective complex with localization
inverts all quasi-isomorphisms. -/
theorem tensorLeftThenQ_inverts_quasiIso
    (P : CC A) [∀ n, Projective (P.X n)] :
    (W A).IsInvertedBy
      (tensorLeftFunctor A P ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  intro X Y φ hφ
  letI : QuasiIso φ := hφ
  letI : QuasiIso ((tensorLeftFunctor A P).map φ) :=
    tensorLeftFunctor_map_quasiIso A P φ
  apply Localization.inverts HomologicalComplexUpToQuasiIso.Q (W A)
  change QuasiIso ((tensorLeftFunctor A P).map φ)
  infer_instance

/-- Derived total left tensor by a fixed componentwise-projective nonnegative complex. -/
noncomputable def derivedTensorLeft
    (P : CC A) [∀ n, Projective (P.X n)] : DerivedCC A ⥤ DerivedCC A :=
  Localization.lift
    (tensorLeftFunctor A P ⋙ HomologicalComplexUpToQuasiIso.Q)
    (tensorLeftThenQ_inverts_quasiIso A P)
    HomologicalComplexUpToQuasiIso.Q

/-- Derived left tensor is canonically induced by chain-level total left tensor. -/
noncomputable def derivedTensorLeftFactors
    (P : CC A) [∀ n, Projective (P.X n)] :
    HomologicalComplexUpToQuasiIso.Q ⋙ derivedTensorLeft A P ≅
      tensorLeftFunctor A P ⋙ HomologicalComplexUpToQuasiIso.Q :=
  Localization.fac _ (tensorLeftThenQ_inverts_quasiIso A P)
    HomologicalComplexUpToQuasiIso.Q

end GaloisForLFunctions.IrregularStokes.ProjectiveDerivedTensor
