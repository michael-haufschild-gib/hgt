import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.CCM.CCMCumulativeNegativeMassSpectrum
import GaloisForLFunctions.RHTower.CCM.CCMRectangularNegativeChannelSpectrum

/-!
# Xi transverse spectral universality

The terminal transverse-width classifiers in the Hedenmalm, source-continuation,
negative-channel, cumulative-mass, projective, and thermal charts all carry the same datum.  This
module packages their maximal common closure without choosing one chart as the definition of the
law.
-/

open Filter

namespace RHTower

noncomputable section

/-- Simultaneous realization of one positive transverse Xi width in all currently formalized
Hedenmalm, analytic-source, negative-channel, cumulative-mass, projective, and thermal charts. -/
def XiTransverseUniversalCertificate
    (tau L alpha : ℝ) (N : ℕ) (a b : ℕ → ℝ) : Prop :=
  HedenmalmGaussianHankelTailCone tau alpha ∧
  InverseTiltedDyadicSourceAnalyticAbove alpha ∧
  CriticalMellinDefectAnalyticAbove alpha ∧
  (∃ N' : ℕ,
    (∀ n : ℕ, N' ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) ∧
    XiRectangularWeilTailPowerLower L N' alpha) ∧
  XiRectangularNegativeChannelEnergyAbove alpha a ∧
  XiRectangularSubpowerChannelAbove alpha b ∧
  XiRectangularNegativeChannelEnergyAbove alpha
    (xiRectangularWeilTailNegativePart L N) ∧
  XiRectangularNegativeChannelEnergyAbove alpha
    (xiRectangularPrimeGammaTailNegativePart L N) ∧
  (∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ))
      (((1 + alpha + epsilon : ℝ) : ℂ))) ∧
  (∃ m : ℕ → ℝ,
    XiRectangularNegativeEnergyMajorantAbove L N alpha m) ∧
  (∃ c d : ℕ → ℝ,
    XiRectangularNegativeTwoChannelCover L N c d ∧
    XiRectangularNegativeChannelEnergyAbove alpha c ∧
    XiRectangularNegativeChannelEnergyAbove alpha d) ∧
  LSeries.abscissaOfAbsConv
      (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
    ((1 + alpha : ℝ) : EReal) ∧
  LSeries.abscissaOfAbsConv
      (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
    ((1 + alpha : ℝ) : EReal) ∧
  NonnegativeDirichletSummatoryGrowthAt
    (xiRectangularPrimeGammaTailNegativePart L N) (1 + alpha) ∧
  NonnegativeDirichletSummatoryGrowthAt
    (rectangularPrimePolarSourceTailNegativePart L N) (1 + alpha) ∧
  xiProjectiveReflectionRadius ≤ alpha ∧
  (∀ m : ℕ, xiThermalProjectiveMoment m ≤
    normalizedPrimeArchMoment 0 * alpha ^ m) ∧
  (∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
    xiThermalProjectiveMoment m ≤ C * alpha ^ m) ∧
  ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
    xiThermalProjectiveColdPartition k ≤
      C * Real.exp ((k : ℝ) * alpha)

/-- **Xi transverse spectral universality law.**  For every positive transverse scale and every
exact nonnegative two-channel split of the rectangular Xi negative mass, one complete Hedenmalm
Gaussian tail cone is equivalent to simultaneous realization of that scale in ten analytic,
arithmetic, projective, and thermal charts. -/
theorem hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate
    {tau L alpha : ℝ} (htau : 0 < tau) (hL : 0 < L) (halpha : 0 < alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ} (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    HedenmalmGaussianHankelTailCone tau alpha ↔
      XiTransverseUniversalCertificate tau L alpha N a b := by
  constructor
  · intro htail
    have hzeros : XiZeroHalfPlaneBound alpha :=
      (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
        htau halpha.le).1 htail
    have hsup : xiRightTransverseSup ≤ alpha :=
      (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha.le).1
        ((xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
          hL halpha.le).2 hzeros)
    have hchannels :=
      (all_xiZeros_re_le_iff_negativeChannelSpectrum
        hL halpha.le hN hsplit).1 hzeros
    have hmoments :=
      xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le.1 hzeros
    refine ⟨htail,
      (xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove
        halpha.le).1 hzeros,
      (xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove
        halpha.le).1 hzeros,
      (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
        hL halpha.le).2 hzeros,
      hchannels.1,
      hchannels.2,
      (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove
        hL halpha.le hN).1 hzeros,
      (xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove
        hL halpha.le hN).1 hzeros,
      (all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeEnergyAbove
        hL halpha.le hN).1 hzeros,
      (xiRightTransverseSup_le_iff_exists_negativeEnergyMajorantAbove
        hL halpha.le hN).1 hsup,
      (xiRightTransverseSup_le_iff_exists_twoChannelEnergyCoverAbove
        hL halpha.le hN).1 hsup,
      (primeGamma_abscissa_le_iff_forall_thermalProjectiveMoment_le
        hL halpha.le hN).2 hmoments,
      (all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le
        hL halpha.le hN).1 hzeros,
      (xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth
        hL halpha.le hN).1 hzeros,
      (all_xiZeros_re_le_iff_rectangularPrimePolarSource_cumulativeNegativeMassGrowth
        hL halpha.le hN).1 hzeros,
      (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le
        halpha.le).1 hzeros,
      hmoments,
      (xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le
        halpha).1 hzeros,
      xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveColdPartition_le.1 hzeros⟩
  · intro hcertificate
    apply (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
      htau halpha.le).2
    exact (xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove
      halpha.le).2 hcertificate.2.1

end

end RHTower
