import GaloisForLFunctions.RHTower.DeningerArithmeticGeometricJetExhaustion
import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalDivision
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Local analytic division for compact-open arithmetic cohomology

Global Xi division uses every multiplicity-bounded source jet.  Compact-open inverse control needs
the corresponding local statement: jets vanish only at Xi points in an open region, so the
normalized meromorphic quotient is holomorphic on that region.

This file proves that local statement directly from the exact Xi divided chain.  On a connected
region containing one nonzero Xi basepoint, the normalized quotient then satisfies

`Q * XiC = F`

throughout the region.  This is the analytic division brick needed for the constructive
`[DAC_LOCAL_QUOTIENT_OPENNESS]` argument; no global interpolation or RH input is used.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/--
Local removable-singularity theorem for the normalized Xi quotient.

Only the multiplicity-bounded jets at the selected point are required.  When the point is not an
Xi zero, the raw quotient is already analytic there.
-/
theorem deningerNormalizedXiQuotient_analyticAt_of_localJets
    (F : DeningerCompactOpenEntire) (z : ℂ)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        xiSpectralPointSupport rho = z →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    AnalyticAt ℂ (deningerNormalizedXiQuotient F) z := by
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
        hjets q.1 hsupp
          (⟨k, hk⟩ : DeningerArithmeticJetIndex q.1)
      simpa only [
        deningerCompactOpenJet_apply,
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
      hrawMer.toMeromorphicNFOn_eq_self_on_nhdsNE
        (Set.mem_univ z)
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
        (deningerRawXiQuotient F) Set.univ
        (Set.mem_univ z)
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
        hrawMer (Set.mem_univ z)
    have heq :
        toMeromorphicNFAt (deningerRawXiQuotient F) z =
          deningerRawXiQuotient F :=
      toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt
    rw [heq] at hlocal
    exact hrawAn.congr hlocal.symm

/-- Vanishing of the local Xi jets makes the normalized quotient analytic on the whole region. -/
theorem deningerNormalizedXiQuotient_analyticOnNhd_of_localJets
    (F : DeningerCompactOpenEntire) (U : Set ℂ)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        xiSpectralPointSupport rho ∈ U →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    AnalyticOnNhd ℂ (deningerNormalizedXiQuotient F) U := by
  intro z hz
  apply deningerNormalizedXiQuotient_analyticAt_of_localJets
  intro rho hrho k
  exact hjets rho (hrho.symm ▸ hz) k

/--
Exact local Xi division on a connected region.

The basepoint only anchors the analytic identity theorem; Xi is required to be nonzero there.
-/
theorem deningerNormalizedXiQuotient_mul_XiC_eqOn_of_localJets
    (F : DeningerCompactOpenEntire) (U : Set ℂ)
    (hU : IsPreconnected U)
    {z0 : ℂ} (hz0 : z0 ∈ U) (hXi0 : XiC z0 ≠ 0)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        xiSpectralPointSupport rho ∈ U →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    Set.EqOn
      (deningerNormalizedXiQuotient F * XiC)
      (F : ℂ → ℂ) U := by
  have hquotientAn :=
    deningerNormalizedXiQuotient_analyticOnNhd_of_localJets
      F U hjets
  have hrawAn0 :
      AnalyticAt ℂ (deningerRawXiQuotient F) z0 :=
    (F.2.analyticAt z0).div
      (XiC_analytic z0 (Set.mem_univ z0)) hXi0
  have hQraw :
      deningerNormalizedXiQuotient F =ᶠ[𝓝 z0]
        deningerRawXiQuotient F := by
    have hlocal :=
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
        (deningerRawXiQuotient_meromorphic F)
        (Set.mem_univ z0)
    have heq :
        toMeromorphicNFAt (deningerRawXiQuotient F) z0 =
          deningerRawXiQuotient F :=
      toMeromorphicNFAt_eq_self.mpr hrawAn0.meromorphicNFAt
    rw [heq] at hlocal
    exact hlocal
  have hXiNe : ∀ᶠ z in 𝓝 z0, XiC z ≠ 0 :=
    (XiC_analytic z0 (Set.mem_univ z0)).continuousAt.eventually_ne
      hXi0
  have hlocal :
      deningerNormalizedXiQuotient F * XiC =ᶠ[𝓝 z0]
        (F : ℂ → ℂ) := by
    filter_upwards [hQraw, hXiNe] with z hq hXi
    simp only [Pi.mul_apply]
    rw [hq, deningerRawXiQuotient,
      div_mul_cancel₀ _ hXi]
  exact
    (hquotientAn.mul
      (fun z _ => XiC_analytic z (Set.mem_univ z)))
      |>.eqOn_of_preconnected_of_eventuallyEq
        (fun z _ => F.2.analyticAt z) hU hz0 hlocal

/-- Closed-disk local division, with the identity asserted on the corresponding open disk. -/
theorem deningerNormalizedXiQuotient_mul_XiC_eqOn_ball
    (F : DeningerCompactOpenEntire) {R : ℝ} (hR : 0 < R)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        ‖xiSpectralPointSupport rho‖ < R →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    Set.EqOn
      (deningerNormalizedXiQuotient F * XiC)
      (F : ℂ → ℂ) (Metric.ball 0 R) := by
  apply
    deningerNormalizedXiQuotient_mul_XiC_eqOn_of_localJets
      F (Metric.ball 0 R) Metric.isPreconnected_ball
      (Metric.mem_ball_self hR) XiC_zero_ne
  intro rho hrho
  exact hjets rho (by simpa [Metric.mem_ball] using hrho)

end

end RHTower
