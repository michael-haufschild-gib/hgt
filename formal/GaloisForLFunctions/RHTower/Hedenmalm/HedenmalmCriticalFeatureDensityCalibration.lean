import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacityAsymptotic

/-!
# Exact density calibration of the HCF source covariance

The canonical HCF phase covariance detects `4π` times off-line multiplicity.  This module turns
that detector into an exact equivalence at every proposed critical-line density, so later source
estimates can be read directly as proportion theorems without repeating asymptotic algebra.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Exact calibration of the canonical HCF covariance at every proposed critical-line density.
The covariance constant is `4π` times the complementary off-line proportion. -/
theorem criticalFeaturePhaseCovariance_four_pi_complement_upper_iff_criticalLine_lower
    (a : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage
        (4 * Real.pi * (1 - a)) ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCanonicalCriticalLineCount a := by
  let D : ℕ → ℝ := fun n =>
    4 * Real.pi *
      (criticalFeatureCanonicalZeroCount n -
        criticalFeatureCanonicalCriticalLineCount n)
  have htransfer :
      CriticalFeatureCanonicalAsymptoticUpper
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage
          (4 * Real.pi * (1 - a)) ↔
        CriticalFeatureCanonicalAsymptoticUpper D (4 * Real.pi * (1 - a)) :=
    criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
      tendsto_criticalFeaturePhaseCovariance_sub_four_pi_mul_offLineMass_div_zeroCount
  rw [htransfer]
  constructor
  · intro hupper ε hε
    have hD := hupper (4 * Real.pi * ε) (by positivity)
    filter_upwards [hD, eventually_criticalFeatureCanonicalZeroCount_pos] with n hDn hN
    dsimp [D] at hDn
    nlinarith [Real.pi_pos]
  · intro hlower ε hε
    have hline := hlower (ε / (4 * Real.pi)) (by positivity)
    filter_upwards [hline, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hlineN hN
    dsimp [D]
    have hscaled := mul_le_mul_of_nonneg_left hlineN
      (show 0 ≤ 4 * Real.pi by positivity)
    have hcoef :
        4 * Real.pi * (a - ε / (4 * Real.pi)) =
          4 * Real.pi * a - ε := by
      field_simp
    rw [← mul_assoc, hcoef] at hscaled
    nlinarith [Real.pi_pos]

end

end RHTower
