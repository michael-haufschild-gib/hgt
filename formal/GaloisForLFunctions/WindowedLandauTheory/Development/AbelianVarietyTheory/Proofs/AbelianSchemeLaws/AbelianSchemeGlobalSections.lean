import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperSmoothGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELOrderAction

/-! Pullback of functions and stability under products for abelian schemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}}

/-- Fibre products of abelian schemes are abelian schemes. -/
theorem IsAbelianScheme.tensor {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  haveI := hA.comm
  haveI := hB.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  have h := IsPullback.of_hasPullback A.hom B.hom
  let π : (A ⊗ B).left ⟶ A.left := pullback.fst A.hom B.hom
  haveI hπ : Smooth π := MorphismProperty.of_isPullback (P := @Smooth) h.flip hB.smooth
  have hπ' : IsProper π := MorphismProperty.of_isPullback (P := @IsProper) h.flip hB.proper
  haveI : GeometricallyConnected π :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.flip hB.geomConnected
  exact ⟨inferInstance, MorphismProperty.comp_mem (@Smooth) π A.hom hπ hA.smooth,
    MorphismProperty.comp_mem (@IsProper) π A.hom hπ' hA.proper, GeometricallyConnected.comp π A.hom⟩

/-- The structure morphism of an abelian scheme induces an isomorphism on global functions. -/
theorem IsAbelianScheme.isIso_appTop {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) : IsIso A.hom.appTop := by
  haveI := hA.smooth
  haveI := hA.proper
  haveI := hA.geomConnected
  exact GlobalTheory.GlobalFunctions.isIso_app_of_geometricallyConnected A.hom ⊤

/-- Every unit on the pullback of an abelian scheme comes from the test scheme. -/
theorem IsAbelianScheme.isIso_fst_appTop {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) : IsIso (fst T A).left.appTop := by
  haveI := hA.smooth
  haveI := hA.proper
  haveI := hA.geomConnected
  change IsIso (pullback.fst T.hom A.hom).appTop
  exact GlobalTheory.GlobalFunctions.isIso_app_of_geometricallyConnected (pullback.fst T.hom A.hom) ⊤

end ReciprocityTheory.ChartRestriction.G.Semi
