import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIFrequencyRange
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIFrequencyFloor

/-!
# Uniform outer-frequency control of every final Menon block

The central disc, the Case-II interval, and the Route-T Case-I interval use different cutoffs.
This file joins the latter two at their literal common boundary and uses the already-proved
central-radius domination of every Case-II floor.  The result keeps the terminally clipped actual
block and introduces no analytic premise.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Every actual final-range block is logarithmically small from the common central radius through
the complete Route-T outer range. -/
theorem exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_outer_range :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ w : ℝ,
        menonHarmonicCentralRadius x ≤ |w| →
        |w| ≤ twoRangeTop ((2 : ℝ) / 3) x →
        ‖harmonicPrimeBlockPoly
            (primesRange (menonFinalRangeBlockLowerNat x j)
              (menonFinalRangeActualBlockUpperNat x j)) w‖ ≤
          C / (Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (20 : ℕ) := by
  obtain ⟨C0, hC0, hcaseII⟩ :=
    exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_caseII_range
  obtain ⟨C1, hC1, hcaseI⟩ :=
    exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_caseI_range
  let C : ℝ := menonHarmonicCaseIIThresholdConstant C0 + C1
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (menonHarmonicCaseIIThresholdConstant_nonneg hC0) hC1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcaseII, hcaseI,
    eventually_menonHarmonicCaseIIFrequencyFloor_le_central,
    eventually_menonFinalRangeActualBlock_caseII_endpoints] with
      x hII hI hfloor hendpoints
  intro j hj w hwLower hwUpper
  let a : ℕ := menonFinalRangeBlockLowerNat x j
  let d : ℝ := (Real.log (a : ℝ)) ^ (20 : ℕ)
  have haLarge : (64 : ℕ) ^ (8 : ℕ) ≤ a := by
    simpa only [a] using (hendpoints j hj).1
  have haOne : 1 < a := by omega
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast haOne)
  have hd0 : 0 < d := by
    dsimp only [d]
    positivity
  have hfreqLower :
      menonHarmonicCaseIIFrequencyFloor a ≤ 2 * Real.pi * |w| := by
    calc
      menonHarmonicCaseIIFrequencyFloor a ≤
          2 * Real.pi * menonHarmonicCentralRadius x := by
            simpa only [a] using hfloor j hj
      _ ≤ 2 * Real.pi * |w| :=
        mul_le_mul_of_nonneg_left hwLower (by positivity)
  rcases le_total (2 * Real.pi * |w|)
      (menonHarmonicCaseIIFrequencyCeiling a) with hbelow | habove
  · have hbound := hII j hj w
      (by simpa only [a] using hfreqLower)
      (by simpa only [a] using hbelow)
    have hmono : menonHarmonicCaseIIThresholdConstant C0 / d ≤ C / d := by
      exact div_le_div_of_nonneg_right
        (by dsimp only [C]; linarith) hd0.le
    exact hbound.trans (by simpa only [a, d] using hmono)
  · have hbound := hI j hj w
      (by simpa only [a] using habove) hwUpper
    have hmono : C1 / d ≤ C / d := by
      exact div_le_div_of_nonneg_right
        (by
          dsimp only [C]
          have := menonHarmonicCaseIIThresholdConstant_nonneg hC0
          linarith) hd0.le
    exact hbound.trans (by simpa only [a, d] using hmono)

/-- Geometric-ladder form of the uniform outer-frequency estimate. -/
theorem exists_absolute_eventually_norm_menonFinalRangeBlock_le_logPow_of_outer_range :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ w : ℝ,
        menonHarmonicCentralRadius x ≤ |w| →
        |w| ≤ twoRangeTop ((2 : ℝ) / 3) x →
        ‖harmonicPrimeBlockPoly
            (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
              (1 + menonFinalRangeLadderEta x) j) w‖ ≤
          C / (Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (20 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_outer_range
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_menonFinalRangeLadder_basic] with x hboundx hbasic
  intro j hj w hwLower hwUpper
  rw [geomBlock_menonFinalRangePrimes_eq_actualBlock hbasic.2.2.2.2.1]
  exact hboundx j hj w hwLower hwUpper

end

end RHTower.Sieve
