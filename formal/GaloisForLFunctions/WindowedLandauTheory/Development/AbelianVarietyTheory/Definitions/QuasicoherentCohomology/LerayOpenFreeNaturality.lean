import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayOpenFreeComparison

/-! The free-sheaf model of the Leray comparison is natural in the
coefficient sheaf. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {X : TopCat.{0}} {ι : Type} [DecidableEq ι] [LinearOrder ι]
  {V W : Opens X} {U : ι → Opens X}

local instance : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

theorem lerayOpenFreeEquiv_natural (hcov : V ≤ ⨆ i, U i) (hW : coverInter V U ∅ = W)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : CoverAcyclic V U F) (hG : CoverAcyclic V U G)
    (φ : F ⟶ G) (n : ℕ) (x : (sheafCechComplex V U F).homology n) :
    lerayOpenFreeEquiv hcov hW G hG n (HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) n x) =
      (lerayOpenFreeEquiv hcov hW F hF n x).comp (Ext.mk₀ φ) (add_zero n) := by
  subst W
  change deningerToOpenFreeExt _ G n (lerayCechEquiv hcov n G hG
      (HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) n x)) =
    (deningerToOpenFreeExt _ F n (lerayCechEquiv hcov n F hF x)).comp (Ext.mk₀ φ) (add_zero n)
  rw [lerayCechEquiv_natural hcov n hF hG φ x, deningerToOpenFreeExt_comp]

end GlobalTheory.SchemeCohomology
