import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureZeta23Baseline
import GaloisForLFunctions.IncommensurableGaborPinching.CriticalLineZeroProportion

/-!
# The improved critical-line census as a source covariance ceiling

The simple-zero proportion `67250071/100000000` gives the complementary
ceiling `4π(1−67250071/100000000)` for the canonical source covariance and
its corrected budget. Both bounds are unconditional.
-/

open Filter Topology RHTower

noncomputable section
namespace GaloisForLFunctions.SquareRootThreshold.Census

/-- The improved simple-zero census supplies the same floor for all critical zeros. -/
theorem criticalFeatureCanonicalCriticalLineCount_67250071_lower :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (67250071 / 100000000) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    IncommensurableGaborPinching.simple_critical_proportion_ge_67250071 ε hε
  filter_upwards [eventually_ge_atTop ⌈T₀⌉₊] with n hn
  have hT : T₀ ≤ (n : ℝ) :=
    (Nat.le_ceil T₀).trans (by exact_mod_cast hn)
  have hsimple :
      (67250071 / 100000000 - ε) * (xiPosZeroCount (n : ℝ) : ℝ) ≤
        (xiSimpleCriticalZeroCount (n : ℝ) : ℝ) := by
    simpa only [zeta23_Ncount_zero_eq_xiPosZeroCount,
      zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ (n : ℝ) hT
  have hcritical :
      (67250071 / 100000000 - ε) * (xiPosZeroCount (n : ℝ) : ℝ) ≤
        (xiPosCriticalZeroCount (n : ℝ) : ℝ) :=
    hsimple.trans (by
      exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount (n : ℝ))
  rw [criticalFeatureCanonicalCriticalLineCount_eq_xiPosCriticalZeroCount]
  have hcount : criticalFeatureCanonicalZeroCount n = (xiPosZeroCount (n : ℝ) : ℝ) := by
    unfold criticalFeatureCanonicalZeroCount
    exact_mod_cast
      (xiPosZeroCount_eq_xiZeroCount (by positivity : (0 : ℝ) ≤ n)).symm
  rwa [hcount]

/-- The covariance ceiling corresponding to the improved unconditional census. -/
theorem criticalFeaturePhaseCovariance_67250071_upper :
    CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage
      (4 * Real.pi * (1 - 67250071 / 100000000)) :=
  (criticalFeaturePhaseCovariance_four_pi_complement_upper_iff_criticalLine_lower
    (67250071 / 100000000)).2 criticalFeatureCanonicalCriticalLineCount_67250071_lower

/-- Source-selected phase correction preserves the improved covariance ceiling. -/
theorem criticalFeatureSourcePhaseCorrectedBudget_67250071_upper :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
        (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
        (criticalFeatureCanonicalLatticeWindow n))
      (4 * Real.pi * (1 - 67250071 / 100000000)) :=
  canonical_sourcePhaseCorrectedBudget_ceiling_of_phaseAverage
    criticalFeaturePhaseCovariance_67250071_upper

/-- The new census strictly improves the two-thirds covariance baseline. -/
theorem census_covariance_ceiling_lt_four_pi_thirds :
    4 * Real.pi * (1 - 67250071 / 100000000) < 4 * Real.pi / 3 := by
  nlinarith only [Real.pi_pos]

#print axioms criticalFeatureCanonicalCriticalLineCount_67250071_lower
#print axioms criticalFeaturePhaseCovariance_67250071_upper
#print axioms criticalFeatureSourcePhaseCorrectedBudget_67250071_upper
#print axioms census_covariance_ceiling_lt_four_pi_thirds

end GaloisForLFunctions.SquareRootThreshold.Census
