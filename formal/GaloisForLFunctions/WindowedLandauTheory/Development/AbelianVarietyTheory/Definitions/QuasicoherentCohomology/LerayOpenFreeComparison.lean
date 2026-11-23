import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayBoundaryNaturality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleCechComparison

/-! The Leray comparison with Ext out of the free sheaf on the covered open. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {X : TopCat.{0}} {ι : Type} [DecidableEq ι] [LinearOrder ι]
  {V W : Opens X} {U : ι → Opens X}

local instance lerayOpenFreeHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

/-- The two free-sheaf models yield the same Leray comparison on the covered open. -/
def lerayOpenFreeEquiv (hcov : V ≤ ⨆ i, U i) (hW : coverInter V U ∅ = W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hF : CoverAcyclic V U F) (n : ℕ) :
    (sheafCechComplex V U F).homology n ≃+ Ext (openFree W) F n :=
  hW ▸ (lerayCechEquiv hcov n F hF).trans (deningerToOpenFreeExt (coverInter V U ∅) F n)

theorem lerayOpenFreeEquiv_zero (hcov : V ≤ ⨆ i, U i) (hW : coverInter V U ∅ = W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hF : CoverAcyclic V U F)
    (z : (sheafCech F V U).obj ∅) :
    lerayOpenFreeEquiv hcov hW F hF 0 (sectionsToCechH0 F hcov z) =
      Ext.mk₀ ((openFreeHomEquiv W F).symm (F.1.map (eqToHom hW.symm).op z)) := by
  subst W
  change deningerToOpenFreeExt _ F 0
    (lerayCechEquiv hcov 0 F hF (sectionsToCechH0 F hcov z)) = _
  rw [lerayCechEquiv_zero_sections, deningerToOpenFreeExt_section]
  simp only [eqToHom_refl, op_id]
  have hz := ConcreteCategory.congr_hom (F.1.map_id (op (coverInter V U ∅))) z
  exact congrArg (fun a => Ext.mk₀ ((openFreeHomEquiv (coverInter V U ∅) F).symm a)) hz.symm

/-- The comparison with Ext preserves the connecting map. -/
theorem lerayOpenFreeEquiv_boundary (hcov : V ≤ ⨆ i, U i) (hW : coverInter V U ∅ = W)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (h₁ : CoverAcyclic V U S.X₁) (h₃ : CoverAcyclic V U S.X₃)
    (n : ℕ) (x : (sheafCechComplex V U S.X₃).homology n) :
    lerayOpenFreeEquiv hcov hW S.X₁ h₁ (n + 1)
      ((coverCech_shortExact hS h₁).δ n (n + 1) rfl x) =
        (lerayOpenFreeEquiv hcov hW S.X₃ h₃ n x).comp hS.extClass rfl := by
  subst W
  change deningerToOpenFreeExt _ S.X₁ (n + 1)
    (lerayCechEquiv hcov (n + 1) S.X₁ h₁ ((coverCech_shortExact hS h₁).δ n (n + 1) rfl x)) =
      (deningerToOpenFreeExt _ S.X₃ n (lerayCechEquiv hcov n S.X₃ h₃ x)).comp hS.extClass rfl
  rw [deningerToOpenFreeExt_comp, lerayCechEquiv_boundary]

end GlobalTheory.SchemeCohomology
