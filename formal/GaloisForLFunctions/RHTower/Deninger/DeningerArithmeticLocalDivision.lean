import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticGeometricJetExhaustion
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticGlobalDivision
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Local analytic division for compact-open arithmetic cohomology

Global Xi division uses every multiplicity-bounded source jet.  Compact-open inverse control needs
the corresponding local statement: jets vanish only at Xi points in an open region, so the
normalized meromorphic quotient is holomorphic on that region.

This file propagates the pointwise removable-singularity statement of `GlobalDivision` across a
region.  On a connected region containing one nonzero Xi basepoint, the normalized quotient then
satisfies

`Q * XiC = F`

throughout the region.  This is the analytic division brick needed for the constructive
`[DAC_LOCAL_QUOTIENT_OPENNESS]` argument; no global interpolation or RH input is used.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

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
