import GaloisForLFunctions.RHTower.CCMRestrictedWeilMixedSourceForm
import GaloisForLFunctions.RHTower.SuzukiBoundaryLayerFormCore

/-!
# Complex smooth core of the exact CCM archimedean form domain

The existing core realization was restricted to real sources.  This module supplies the literal
complex version needed by mixed Weil pairings.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap
noncomputable section
namespace RHTower

/-- Every complex smooth compactly supported strict-interior test belongs to the literal CCM
form domain. -/
theorem exists_ccmArchimedeanFormDomain_eq_smoothComplexTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∃ f : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormEmbedding a f = suzukiComplexTestL2 g hgdiff hgsupp := by
  let G : SchwartzMap ℝ ℂ := suzukiComplexTestSchwartz g hgdiff hgsupp
  let F : SchwartzMap ℝ ℂ := 𝓕 G
  let hF : MemLp (F : ℝ → ℂ) 2 ccmArchimedeanFormMeasure :=
    F.memLp_two_ccmArchimedeanFormMeasure
  let w : CCMArchimedeanFourierL2 := hF.toLp F
  have hwToL2 : ccmArchimedeanWeightedToL2 w = F.toLp 2 volume := by
    apply Lp.ext
    have hwFweighted : (w : ℝ → ℂ) =ᵐ[ccmArchimedeanFormMeasure] F := hF.coeFn_toLp
    have hwFvolume : (w : ℝ → ℂ) =ᵐ[volume] F :=
      hwFweighted.filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn w, hwFvolume,
      F.coeFn_toLp 2 volume] with x hw hFv hFL2
    rw [hw, hFv, hFL2]
  have htime : ccmArchimedeanFourierToTime w = G.toLp 2 volume := by
    apply fourierUnitary.injective
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hwToL2]
    exact (SchwartzMap.toLp_fourier_eq G).symm
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (G.toLp 2 volume) = G.toLp 2 volume := by
    apply Lp.ext
    have hcoeG : (G.toLp 2 volume : ℝ → ℂ) =ᵐ[volume] g := by
      simpa [G, suzukiComplexTestL2] using
        suzukiComplexTestL2_coeFn g hgdiff hgsupp
    filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1) (G.toLp 2 volume),
      hcoeG] with x hcut hcoe
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hcoe]
      have hgzero : g x = 0 := by
        apply Function.notMem_support.mp
        intro hxg
        apply hx
        exact Ioo_subset_Icc_self (hgaper (subset_tsupport g hxg))
      rw [hgzero]
  have hwker : w ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (ccmArchimedeanFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self, hfix, sub_self]
  refine ⟨⟨w, hwker⟩, ?_⟩
  change ccmArchimedeanFourierToTime w = suzukiComplexTestL2 g hgdiff hgsupp
  exact htime

/-- Canonical exact CCM form vector of a strict-interior complex smooth source. -/
def ccmComplexSmoothFormVector
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    CCMArchimedeanFormDomain a :=
  Classical.choose
    (exists_ccmArchimedeanFormDomain_eq_smoothComplexTest
      a g hgdiff hgsupp hgaper)

theorem ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ccmArchimedeanFormEmbedding a
        (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper) =
      suzukiComplexTestL2 g hgdiff hgsupp :=
  Classical.choose_spec
    (exists_ccmArchimedeanFormDomain_eq_smoothComplexTest
      a g hgdiff hgsupp hgaper)

/-- Physical representative of the complex smooth-core vector. -/
theorem ccmArchimedeanFormToAperture_ccmComplexSmoothFormVector_coeFn
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ((ccmArchimedeanFormToAperture a
      (ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper) : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] g := by
  rw [ccmArchimedeanFormToAperture_coe,
    ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector]
  exact suzukiComplexTestL2_coeFn g hgdiff hgsupp

/-- Fourier coordinate stored by the complex smooth-core vector. -/
theorem ccmComplexSmoothFormVector_coeFn
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (hgaper : tsupport g ⊆ Ioo (-a.1) a.1) :
    ((ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper).1 : ℝ → ℂ)
      =ᵐ[volume]
        𝓕 (suzukiComplexTestSchwartz g hgdiff hgsupp : ℝ → ℂ) := by
  let q := ccmComplexSmoothFormVector a g hgdiff hgsupp hgaper
  let U := suzukiComplexTestSchwartz g hgdiff hgsupp
  have hphysical :=
    ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector
      a g hgdiff hgsupp hgaper
  have hweighted : ccmArchimedeanWeightedToL2 q.1 =
      (𝓕 U : SchwartzMap ℝ ℂ).toLp 2 volume := by
    calc
      ccmArchimedeanWeightedToL2 q.1 =
          fourierUnitary (ccmArchimedeanFormEmbedding a q) :=
        (fourierUnitary_ccmArchimedeanFourierToTime q.1).symm
      _ = fourierUnitary (suzukiComplexTestL2 g hgdiff hgsupp) := by
        rw [hphysical]
      _ = fourierUnitary (U.toLp 2 volume) := by rfl
      _ = (𝓕 U : SchwartzMap ℝ ℂ).toLp 2 volume :=
        SchwartzMap.toLp_fourier_eq U
  have hw := ccmArchimedeanWeightedToL2_coeFn q.1
  rw [hweighted] at hw
  exact hw.symm.trans ((𝓕 U : SchwartzMap ℝ ℂ).coeFn_toLp 2 volume)

end RHTower
