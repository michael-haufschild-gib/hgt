import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayOpenFreeNaturality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverLerayComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayPushforwardComparison

/-! Leray comparisons for scheme modules commute with coefficient maps,
restriction to a subcover, and the direct-image comparison. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace
open HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {X Y : Scheme.{0}} {ι κ : Type} [DecidableEq ι] [LinearOrder ι]
  {V W : X.Opens} {U : ι → X.Opens}

private abbrev underlying {X : Scheme.{0}} := SheafOfModules.toSheaf X.ringCatSheaf

local instance : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X.carrier) :=
  hasExt_of_enoughInjectives _

/-- Use a specified equal open as the target of the linear Leray comparison. -/
def moduleLerayLinearEquivAt (M : X.Modules) (n : ℕ) (hcov : V ≤ ⨆ i, U i)
    (hW : coverInter V U ∅ = W) (hM : CoverAcyclic V U (underlying.obj M)) :
    ModuleCechCohomology V U M n ≃ₗ[Γ(X, ⊤)] CohomologyOn M W n :=
  hW ▸ moduleLerayLinearEquiv V U M n hcov hM

theorem moduleLerayLinearEquivAt_apply (M : X.Modules) (n : ℕ) (hcov : V ≤ ⨆ i, U i)
    (hW : coverInter V U ∅ = W) (hM : CoverAcyclic V U (underlying.obj M))
    (x : ModuleCechCohomology V U M n) :
    moduleLerayLinearEquivAt M n hcov hW hM x =
      lerayOpenFreeEquiv hcov hW (underlying.obj M) hM n x := by
  subst W
  rfl

theorem moduleLerayLinearEquivAt_natural {M N : X.Modules} (φ : M ⟶ N) (n : ℕ)
    (hcov : V ≤ ⨆ i, U i) (hW : coverInter V U ∅ = W)
    (hM : CoverAcyclic V U (underlying.obj M)) (hN : CoverAcyclic V U (underlying.obj N))
    (x : ModuleCechCohomology V U M n) :
    moduleLerayLinearEquivAt N n hcov hW hN
      (HomologicalComplex.homologyMap (sheafCechComplexMap V U (underlying.map φ)) n x) =
        CohomologyOn.map φ W n (moduleLerayLinearEquivAt M n hcov hW hM x) := by
  rw [moduleLerayLinearEquivAt_apply, moduleLerayLinearEquivAt_apply]
  exact lerayOpenFreeEquiv_natural hcov hW hM hN (underlying.map φ) n x

theorem moduleLerayLinearEquivAt_subcover [DecidableEq κ] [LinearOrder κ] (j : κ ↪o ι)
    (M : X.Modules) (n : ℕ) (h₁ : V ≤ ⨆ i, U i) (h₂ : V ≤ ⨆ i, (U ∘ j) i)
    (hM : CoverAcyclic V U (underlying.obj M)) (hM' : CoverAcyclic V (U ∘ j) (underlying.obj M))
    (x : ModuleCechCohomology V U M n) :
    moduleLerayLinearEquivAt M n h₂ (coverInter_empty V (U ∘ j)) hM'
        (HomologicalComplex.homologyMap (subcoverCechMap V U j (underlying.obj M)) n x) =
      moduleLerayLinearEquivAt M n h₁ (coverInter_empty V U) hM x := by
  rw [moduleLerayLinearEquivAt_apply, moduleLerayLinearEquivAt_apply]
  exact lerayOpenFreeEquiv_subcover j h₁ h₂ n (underlying.obj M) hM hM' x

/-- Leray comparison for a direct image of a module along inverse-image covers. -/
theorem moduleLerayLinearEquivAt_pushforward (f : Y ⟶ X) {B : Set X.Opens}
    (hB : Opens.IsBasis B) (hU : ∀ I : Finset ι, I.Nonempty → coverInter V U I ∈ B)
    (hcov : V ≤ ⨆ i, U i) (M : Y.Modules) (hM : AcyclicOnPreimages f.base B (underlying.obj M))
    (hX : CoverAcyclic V U (underlying.obj ((Scheme.Modules.pushforward f).obj M)))
    (hY : CoverAcyclic (f ⁻¹ᵁ V) (fun i => f ⁻¹ᵁ U i) (underlying.obj M))
    (n : ℕ) (x : ModuleCechCohomology V U ((Scheme.Modules.pushforward f).obj M) n) :
    CohomologyOn.pushforwardComparison f M V n
      (moduleLerayLinearEquivAt _ n hcov (coverInter_empty V U) hX x) =
    moduleLerayLinearEquivAt M n (preimage_cover_le f.base V U hcov)
      (coverInter_empty (f ⁻¹ᵁ V) (fun i => f ⁻¹ᵁ U i)) hY
      (HomologicalComplex.homologyMap (pushforwardCechIso f.base V U (underlying.obj M)).hom n x) := by
  rw [moduleLerayLinearEquivAt_apply, moduleLerayLinearEquivAt_apply]
  let G := underlying.obj M
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f.base
  have key (W' : X.Opens) (hW' : coverInter V U ∅ = W') :
      abelianPushforwardComparison f.base G W' n
        (lerayOpenFreeEquiv hcov hW' (P.obj G) hX n x) =
      lerayOpenFreeEquiv (preimage_cover_le f.base V U hcov)
        ((preimage_coverInter f.base V U ∅).symm.trans (congrArg (fun O : X.Opens => f ⁻¹ᵁ O) hW'))
        G hY n (HomologicalComplex.homologyMap (pushforwardCechIso f.base V U G).hom n x) := by
    subst W'
    exact lerayOpenFreeEquiv_pushforward f.base hB hU hcov G hM n x
  exact key V (coverInter_empty V U)

end GlobalTheory.SchemeCohomology
