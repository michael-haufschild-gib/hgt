import GaloisForLFunctions.RHTower.XiHurwitzPrincipalPhaseGrowth
import GaloisForLFunctions.RHTower.XiTransverseSpectralUniversalityLaw

/-!
# Xi--Hurwitz full transverse aperture spectrum

The supremal principal Hurwitz monodromy phase is already the sharp exponent of one rectangular
Weil observable.  Independently, the transverse universal certificate synchronizes eighteen
Hedenmalm, analytic-source, negative-channel, cumulative-mass, projective, and thermal charts at
each positive aperture.

This module computes the parameter spectrum of that complete certificate.  At every positive
aperture it holds exactly above the supremal Hurwitz phase.  When the right Xi divisor is
nonempty, the complete admissible aperture set is therefore the closed upper ray beginning at
that intrinsic HGT phase.
-/

open Complex Filter Function Set LSeries
open scoped Topology ENNReal

namespace RHTower

noncomputable section

/-- The full transverse certificate has the supremal principal Hurwitz monodromy phase as its
exact positive-aperture threshold. -/
theorem xiTransverseUniversalCertificate_iff_hurwitzPrincipalPhaseSup_le
    {tau L alpha : ℝ} (htau : 0 < tau) (hL : 0 < L) (halpha : 0 < alpha)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ} (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    XiTransverseUniversalCertificate tau L alpha N a b ↔
      xiHurwitzRightPrincipalPhaseSup ≤ alpha := by
  have hzeroSup :
      XiZeroHalfPlaneBound alpha ↔ xiRightTransverseSup ≤ alpha :=
    (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
      hL halpha.le).symm.trans
      (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha.le)
  have hcertificate :
      XiTransverseUniversalCertificate tau L alpha N a b ↔
        xiRightTransverseSup ≤ alpha :=
    (hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate
      htau hL halpha hN hsplit).symm.trans
      ((hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
        htau halpha.le).trans hzeroSup)
  simpa only [xiHurwitzRightPrincipalPhaseSup_eq_transverseSup] using
    hcertificate

/-- Positive apertures carrying the complete transverse certificate. -/
def XiHurwitzFullTransverseApertureSpectrum
    (tau L : ℝ) (N : ℕ) (a b : ℕ → ℝ) : Set ℝ :=
  {alpha : ℝ | 0 < alpha ∧
    XiTransverseUniversalCertificate tau L alpha N a b}

/-- **Xi--Hurwitz full transverse aperture-spectrum universality law.**  If the right Xi divisor
is nonempty, the positive apertures simultaneously supporting all eighteen transverse charts form
the closed upper ray whose left endpoint is the supremal principal Hurwitz phase. -/
theorem xiHurwitzFullTransverseApertureSpectrum_eq_Ici_principalPhaseSup
    {tau L : ℝ} (htau : 0 < tau) (hL : 0 < L)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ} (hsplit : XiRectangularNegativeChannelSplit L N a b)
    (hne : Nonempty XiRightZeroCopy) :
    XiHurwitzFullTransverseApertureSpectrum tau L N a b =
      Set.Ici xiHurwitzRightPrincipalPhaseSup := by
  ext alpha
  simp only [XiHurwitzFullTransverseApertureSpectrum,
    Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨halpha, hcertificate⟩
    exact
      (xiTransverseUniversalCertificate_iff_hurwitzPrincipalPhaseSup_le
        htau hL halpha hN hsplit).mp hcertificate
  · intro hphase
    have hphasePos : 0 < xiHurwitzRightPrincipalPhaseSup := by
      rw [xiHurwitzRightPrincipalPhaseSup_eq_transverseSup]
      exact xiRightTransverseSup_pos hne
    have halpha : 0 < alpha := hphasePos.trans_le hphase
    exact ⟨halpha,
      (xiTransverseUniversalCertificate_iff_hurwitzPrincipalPhaseSup_le
        htau hL halpha hN hsplit).mpr hphase⟩

end

end RHTower
