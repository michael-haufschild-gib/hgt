import GaloisForLFunctions.HTGeometry.StokesExactSheafification
import Mathlib.Algebra.Homology.Localization

/-!
# Derived exact sheafification

Degreewise exact sheafification preserves quasi-isomorphisms of nonnegative integer-module
presheaf complexes. It therefore descends to a functor between the presheaf and sheaf complex
categories localized at quasi-isomorphisms.
-/

open CategoryTheory Limits

universe wₚ wₛ

namespace GaloisForLFunctions.IrregularStokes.DerivedExactSheafification

open ExactSheafification MonoidalSheafTensor OrdinaryConvolution

abbrev PShCC (Y : TopCat.{0}) := IntModulePresheafChainComplex Y

abbrev ShCC (Y : TopCat.{0}) := IntModuleSheafChainComplex Y

abbrev PShW (Y : TopCat.{0}) :=
  HomologicalComplex.quasiIso (TopCat.Presheaf (IntModuleCat.{0}) Y)
    (ComplexShape.down ℕ)

abbrev ShW (Y : TopCat.{0}) :=
  HomologicalComplex.quasiIso (TopCat.Sheaf (IntModuleCat.{0}) Y)
    (ComplexShape.down ℕ)

variable (Y : TopCat.{0})
variable [MorphismProperty.HasLocalization.{wₚ} (PShW Y)]
variable [MorphismProperty.HasLocalization.{wₛ} (ShW Y)]

/-- Nonnegative integer-module presheaf complexes localized at quasi-isomorphisms. -/
abbrev DerivedPShCC :=
  HomologicalComplexUpToQuasiIso
    (TopCat.Presheaf (IntModuleCat.{0}) Y) (ComplexShape.down ℕ)

/-- Nonnegative integer-module sheaf complexes localized at quasi-isomorphisms. -/
abbrev DerivedShCC :=
  HomologicalComplexUpToQuasiIso
    (TopCat.Sheaf (IntModuleCat.{0}) Y) (ComplexShape.down ℕ)

/-- Degreewise sheafification on nonnegative complexes. -/
noncomputable def sheafificationFunctor : PShCC Y ⥤ ShCC Y :=
  (topPresheafToSheaf Y).mapHomologicalComplex (ComplexShape.down ℕ)

omit [MorphismProperty.HasLocalization.{wₚ} (PShW Y)]
  [MorphismProperty.HasLocalization.{wₛ} (ShW Y)] in
/-- Degreewise exact sheafification preserves quasi-isomorphisms. -/
theorem sheafificationFunctor_map_quasiIso
    {K L : PShCC Y} (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso ((sheafificationFunctor Y).map φ) := by
  exact topPresheafToSheaf_map_quasiIso Y φ

omit [MorphismProperty.HasLocalization.{wₚ} (PShW Y)] in
/-- Sheafification followed by localization inverts every presheaf quasi-isomorphism. -/
theorem sheafificationThenQ_inverts_quasiIso :
    (PShW Y).IsInvertedBy
      (sheafificationFunctor Y ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  intro K L φ hφ
  letI : QuasiIso φ := hφ
  letI : QuasiIso ((sheafificationFunctor Y).map φ) :=
    sheafificationFunctor_map_quasiIso Y φ
  apply Localization.inverts HomologicalComplexUpToQuasiIso.Q (ShW Y)
  change QuasiIso ((sheafificationFunctor Y).map φ)
  infer_instance

/-- Degreewise exact sheafification descended to quasi-isomorphism localizations. -/
noncomputable def derivedSheafification : DerivedPShCC Y ⥤ DerivedShCC Y :=
  Localization.lift
    (sheafificationFunctor Y ⋙ HomologicalComplexUpToQuasiIso.Q)
    (sheafificationThenQ_inverts_quasiIso Y)
    HomologicalComplexUpToQuasiIso.Q

/-- Derived sheafification is canonically induced by degreewise chain-level sheafification. -/
noncomputable def derivedSheafificationFactors :
    HomologicalComplexUpToQuasiIso.Q ⋙ derivedSheafification Y ≅
      sheafificationFunctor Y ⋙ HomologicalComplexUpToQuasiIso.Q :=
  Localization.fac _ (sheafificationThenQ_inverts_quasiIso Y)
    HomologicalComplexUpToQuasiIso.Q

end GaloisForLFunctions.IrregularStokes.DerivedExactSheafification
