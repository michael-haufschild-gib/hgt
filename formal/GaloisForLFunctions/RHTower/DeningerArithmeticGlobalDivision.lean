import GaloisForLFunctions.RHTower.DeningerArithmeticJetProduct
import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Global analytic division by Xi

If every jet of an entire function below the corresponding Xi multiplicity vanishes, then the
function is globally divisible by Xi.  The proof normalizes the meromorphic quotient `F / XiC`.
At each Xi zero, finite-order jet vanishing removes the numerator zero, while the canonical Xi
divided chain removes the denominator zero with exactly the same multiplicity.  Meromorphic
normal-form extension fills all removable values simultaneously.

Consequently the Xi differential range is exactly the kernel of the continuous all-jet map and is
closed in the compact-open topology.  This proves `[DAC_GLOBAL_JET_DIVISION]` and
`[DAC_CLOSED_XI_RANGE]` unconditionally; global jet interpolation remains separate.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- Pointwise meromorphic quotient before filling the removable Xi singularities. -/
def deningerRawXiQuotient (F : DeningerCompactOpenEntire) : ℂ → ℂ :=
  fun z => F z / XiC z

theorem deningerRawXiQuotient_meromorphic
    (F : DeningerCompactOpenEntire) :
    MeromorphicOn (deningerRawXiQuotient F) Set.univ :=
  by
    have hF : AnalyticOnNhd ℂ (fun z => F z) Set.univ :=
      fun z _ => F.2.analyticAt z
    exact hF.meromorphicOn.div XiC_analytic.meromorphicOn

/-- Simultaneous removable-singularity filling of the raw Xi quotient. -/
def deningerNormalizedXiQuotient
    (F : DeningerCompactOpenEntire) : ℂ → ℂ :=
  toMeromorphicNFOn (deningerRawXiQuotient F) Set.univ

/--
Vanishing of all multiplicity-bounded Xi jets makes the normalized quotient entire.
-/
theorem deningerNormalizedXiQuotient_analytic
    (F : DeningerCompactOpenEntire)
    (hjets : deningerCompactOpenAllJets F = 0) :
    AnalyticOnNhd ℂ (deningerNormalizedXiQuotient F) Set.univ := by
  intro z hz
  have hrawMer := deningerRawXiQuotient_meromorphic F
  by_cases hXi : XiC z = 0
  · obtain ⟨q, hq⟩ :=
      (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hXi
    have hsupp :
        xiSpectralPointSupport q.1 = z := by
      simpa only [xiSpectralPoint_eq_support] using hq
    let m := xiSupportMultiplicity q.1
    have hvanish :
        ∀ k < m, iteratedDeriv k (F : ℂ → ℂ) z = 0 := by
      intro k hk
      have hcoord :=
        congrFun (congrFun hjets q.1) (⟨k, hk⟩ : DeningerArithmeticJetIndex q.1)
      simpa only [
        deningerCompactOpenAllJets_apply,
        Pi.zero_apply,
        hsupp] using hcoord
    have horder :
        (m : ℕ∞) ≤ analyticOrderAt (F : ℂ → ℂ) z := by
      exact
        (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (F.2.analyticAt z)).mpr hvanish
    obtain ⟨G, hG, hFG⟩ :=
      GaloisForLFunctions.RHTower.BakerProof.exists_entire_factor_of_natCast_le_analyticOrderAt
        (F : ℂ → ℂ) (fun w => F.2.analyticAt w) z m horder
    let H : ℂ → ℂ :=
      xiThetaDividedChain
        (xiSpectralPointSupport q.1) m
    have hH : AnalyticAt ℂ H z := by
      simpa only [H, hsupp] using
        xiThetaDividedChain_analyticAt z m z
    have hH0 : H z ≠ 0 := by
      simpa only [H, hsupp, m] using
        xiThetaDividedChain_nonzero_at_multiplicity q.1
    have hXiFactor :
        ∀ w, XiC w = (w - z) ^ m * H w := by
      intro w
      simpa only [H, hsupp, m] using
        xiThetaDividedChain_factorization q.1 w
    have hGH :
        AnalyticAt ℂ (fun w => G w / H w) z :=
      (hG z).div hH hH0
    have hnormalized_raw :
        deningerNormalizedXiQuotient F =ᶠ[𝓝[≠] z]
          deningerRawXiQuotient F :=
      hrawMer.toMeromorphicNFOn_eq_self_on_nhdsNE hz
    have hraw_GH :
        deningerRawXiQuotient F =ᶠ[𝓝[≠] z]
          fun w => G w / H w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hwz : w ≠ z := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hw
      have hpow : (w - z) ^ m ≠ 0 :=
        pow_ne_zero m (sub_ne_zero.mpr hwz)
      rw [deningerRawXiQuotient, hFG w, hXiFactor w]
      field_simp [hpow]
    have hpunct :
        deningerNormalizedXiQuotient F =ᶠ[𝓝[≠] z]
          fun w => G w / H w :=
      hnormalized_raw.trans hraw_GH
    have hNF :
        MeromorphicNFAt (deningerNormalizedXiQuotient F) z :=
      meromorphicNFOn_toMeromorphicNFOn
        (deningerRawXiQuotient F) Set.univ hz
    have hnear :
        deningerNormalizedXiQuotient F =ᶠ[𝓝 z]
          fun w => G w / H w :=
      (hNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        hGH.meromorphicNFAt).mp hpunct
    exact hGH.congr hnear.symm
  · have hrawAn :
        AnalyticAt ℂ (deningerRawXiQuotient F) z :=
      (F.2.analyticAt z).div
        (XiC_analytic z (Set.mem_univ z)) hXi
    have hlocal :=
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
        hrawMer hz
    have heq :
        toMeromorphicNFAt (deningerRawXiQuotient F) z =
          deningerRawXiQuotient F :=
      toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt
    rw [heq] at hlocal
    exact hrawAn.congr hlocal.symm

/-- Exact entire quotient identity after all removable values have been filled. -/
theorem deningerNormalizedXiQuotient_mul_XiC
    (F : DeningerCompactOpenEntire)
    (hjets : deningerCompactOpenAllJets F = 0) :
    deningerNormalizedXiQuotient F * XiC = (F : ℂ → ℂ) := by
  have hquotientAn :=
    deningerNormalizedXiQuotient_analytic F hjets
  have hrawAn0 :
      AnalyticAt ℂ (deningerRawXiQuotient F) 0 :=
    (F.2.analyticAt 0).div
      (XiC_analytic 0 (Set.mem_univ 0)) XiC_zero_ne
  have hQraw :
      deningerNormalizedXiQuotient F =ᶠ[𝓝 0]
        deningerRawXiQuotient F := by
    have hlocal :=
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
        (deningerRawXiQuotient_meromorphic F)
        (Set.mem_univ (0 : ℂ))
    have heq :
        toMeromorphicNFAt (deningerRawXiQuotient F) 0 =
          deningerRawXiQuotient F :=
      toMeromorphicNFAt_eq_self.mpr hrawAn0.meromorphicNFAt
    rw [heq] at hlocal
    exact hlocal
  have hXiNe : ∀ᶠ z in 𝓝 (0 : ℂ), XiC z ≠ 0 :=
    (XiC_analytic 0 (Set.mem_univ _)).continuousAt.eventually_ne
      XiC_zero_ne
  have hlocal :
      deningerNormalizedXiQuotient F * XiC =ᶠ[𝓝 0]
        (F : ℂ → ℂ) := by
    filter_upwards [hQraw, hXiNe] with z hq hXi
    simp only [Pi.mul_apply]
    rw [hq, deningerRawXiQuotient, div_mul_cancel₀ _ hXi]
  exact
    (hquotientAn.mul XiC_analytic).eq_of_eventuallyEq
      (fun z _ => F.2.analyticAt z) hlocal

/-- The normalized quotient as a compact-open entire source. -/
def deningerCompactOpenXiQuotient
    (F : DeningerCompactOpenEntire)
    (hjets : deningerCompactOpenAllJets F = 0) :
    DeningerCompactOpenEntire :=
  let hdiff : Differentiable ℂ (deningerNormalizedXiQuotient F) :=
    analyticOnNhd_univ_iff_differentiable.mp
      (deningerNormalizedXiQuotient_analytic F hjets)
  ⟨⟨deningerNormalizedXiQuotient F, hdiff.continuous⟩, hdiff⟩

@[simp]
theorem deningerCompactOpenXiQuotient_apply
    (F : DeningerCompactOpenEntire)
    (hjets : deningerCompactOpenAllJets F = 0)
    (z : ℂ) :
    deningerCompactOpenXiQuotient F hjets z =
      deningerNormalizedXiQuotient F z :=
  rfl

/-- The Xi range is exactly the kernel of all multiplicity-bounded jets. -/
theorem deningerCompactOpenXiRange_eq_allJets_ker :
    deningerCompactOpenXiRange =
      deningerCompactOpenAllJets.ker := by
  apply le_antisymm
  · exact deningerCompactOpenXiRange_le_allJets_ker
  · intro F hF
    change deningerCompactOpenAllJets F = 0 at hF
    refine ⟨deningerCompactOpenXiQuotient F hF, ?_⟩
    ext z
    change
      XiC z * deningerNormalizedXiQuotient F z = F z
    have hid :=
      congrFun (deningerNormalizedXiQuotient_mul_XiC F hF) z
    simpa only [Pi.mul_apply, mul_comm] using hid

/-- `[DAC_GLOBAL_JET_DIVISION]` is proved. -/
theorem deningerArithmeticGlobalJetDivision :
    DeningerArithmeticGlobalJetDivision :=
  deningerCompactOpenXiRange_eq_allJets_ker

/-- `[DAC_CLOSED_XI_RANGE]` is proved unconditionally. -/
theorem deningerArithmeticXiRangeClosed :
    DeningerArithmeticXiRangeClosed :=
  deningerArithmeticXiRangeClosed_of_globalJetDivision
    deningerArithmeticGlobalJetDivision

end

end RHTower
