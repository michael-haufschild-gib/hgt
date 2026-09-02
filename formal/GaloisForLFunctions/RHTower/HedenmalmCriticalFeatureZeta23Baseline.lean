import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureDensityCalibration
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureHeightCellPlemeljDomination
import GaloisForLFunctions.RHTower.Zeta23HorizontalSingletonDensity

/-!
# Unconditional Zeta23 baseline for the HCF source covariance

Alpöge--Furman's unconditional two-thirds theorem is stated for the classical positive-height
Xi census.  This module transports it into the canonical HCF asymptotic language and then through
the exact HCF density calibration.  The result is the first unconditional linear ceiling for the
height-cell source covariance and its source-selected corrected budget:

`B_HCF(n) ≤ (4π/3 + o(1)) N(n)`.

This is a baseline, not the three-quarter theorem.  The sharp 75% gate is `π N(n) + o(N(n))`, so
the remaining source work must save `π/3` from this unconditional ceiling.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Alpöge--Furman's two-thirds density, expressed in the canonical HCF census language. -/
theorem criticalFeatureCanonicalCriticalLineCount_twoThirds_lower :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (2 / 3) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_simpleCritical_epsilon ε hε
  filter_upwards [eventually_ge_atTop ⌈T₀⌉₊] with n hn
  have hT : T₀ ≤ (n : ℝ) :=
    (Nat.le_ceil T₀).trans (by exact_mod_cast hn)
  have hsimple := hT₀ (n : ℝ) hT
  have hcritical :
      (2 / 3 - ε) * (xiPosZeroCount (n : ℝ) : ℝ) ≤
        (xiPosCriticalZeroCount (n : ℝ) : ℝ) :=
    hsimple.trans (by
      exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount (n : ℝ))
  rw [criticalFeatureCanonicalCriticalLineCount_eq_xiPosCriticalZeroCount]
  have hcount :
      criticalFeatureCanonicalZeroCount n =
        (xiPosZeroCount (n : ℝ) : ℝ) := by
    unfold criticalFeatureCanonicalZeroCount
    exact_mod_cast
      (xiPosZeroCount_eq_xiZeroCount (by positivity : (0 : ℝ) ≤ n)).symm
  rwa [hcount]

/-- Unconditional HCF phase-covariance ceiling obtained from two-thirds critical-line density. -/
theorem criticalFeaturePhaseCovariance_fourPiThirds_upper :
    CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage
      (4 * Real.pi / 3) := by
  have h :=
    (criticalFeaturePhaseCovariance_four_pi_complement_upper_iff_criticalLine_lower
      (2 / 3)).2 criticalFeatureCanonicalCriticalLineCount_twoThirds_lower
  convert h using 1 <;> ring

/-- The same unconditional ceiling for the corrected HCF budget at its source-selected phase. -/
theorem criticalFeatureSourcePhaseCorrectedBudget_fourPiThirds_upper :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
        (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
        (criticalFeatureCanonicalLatticeWindow n))
      (4 * Real.pi / 3) :=
  canonical_sourcePhaseCorrectedBudget_ceiling_of_phaseAverage
    criticalFeaturePhaseCovariance_fourPiThirds_upper

end

end RHTower
