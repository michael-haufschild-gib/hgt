import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentSixtyFourthFloor
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyOneFourthTraceReduction

/-!
# Centered order-21 source-budget closure

The 64-cell analytic certificates for the dominant theta atom imply an exact
fourth-moment floor.  Combined with the normalized source-mass ceiling and the
centered fourth-trace identity, this empties the order-21 residual annulus and
proves positivity of `normalizedPrimeArchMoment 20` without zero data or
numerical integration.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- The 64-cell lower mass of the dominant atom's fourth moment exceeds `143/50000`. -/
theorem oneHundredFortyThree_div_fiftyThousand_lt_sum_firstAtomFourthLowerMass64 :
    (143 / 50000 : ℝ) <
      ∑ j ∈ Finset.range 56,
        thetaCuspFirstAtomRawLowerIntervalMass64 2 j :=
  (by norm_num : (143 / 50000 : ℝ) < 2951 / 1000000).trans
    twoThousandNineHundredFiftyOne_div_oneMillion_lt_sum_firstAtomFourthLowerMass64

/-- The certified 64-cell mass is an unconditional floor for the dominant atom's fourth moment. -/
theorem oneHundredFortyThree_div_fiftyThousand_lt_thetaCuspAtomRawEvenMoment_two_one :
    (143 / 50000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 :=
  (by norm_num : (143 / 50000 : ℝ) < 2951 / 1000000).trans
    twoThousandNineHundredFiftyOne_div_oneMillion_lt_thetaCuspAtomRawEvenMoment_two_one

/-- Sharpened normalized fourth theta moment forced by the dominant atom. -/
theorem oneHundredFortyThree_div_twentyFiveThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (143 / 25000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  have hraw2 : (143 / 50000 : ℝ) < thetaCuspRawEvenMoment 2 :=
    oneHundredFortyThree_div_fiftyThousand_lt_thetaCuspAtomRawEvenMoment_two_one.trans_le
      (thetaCuspAtomRawEvenMoment_one_le_raw 2)
  have hraw0pos : 0 < thetaCuspRawEvenMoment 0 :=
    thetaCuspRawEvenMoment_zero_pos
  have hraw1nonneg : 0 ≤ thetaCuspRawEvenMoment 1 :=
    thetaCuspRawEvenMoment_nonneg 1
  have hraw0le : thetaCuspRawEvenMoment 0 ≤ 1 / 2 := by
    nlinarith [thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget]
  rw [thetaCuspNormalizedEvenMoment, lt_div_iff₀ hraw0pos]
  nlinarith

/-- The sharpened source data crosses the exact order-21 fourth-trace exclusion threshold. -/
theorem normalizedPrimeArchMoment_one_lt_three_over_twentyFiveThousand :
    normalizedPrimeArchMoment 1 < 3 / 25000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM :=
    normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredThirtyThree_over_oneHundredThousand
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hMsq : M ^ (2 : ℕ) < (4633 / 100000 : ℝ) ^ (2 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr (by simpa only [M] using hM))
      (add_pos (by norm_num : (0 : ℝ) < 4633 / 100000) hM0)
    nlinarith
  have hmu :=
    oneHundredFortyThree_div_twentyFiveThousand_lt_thetaCuspNormalizedEvenMoment_two
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simpa only [M] using (by nlinarith :
    M ^ (2 : ℕ) / 2 - thetaCuspNormalizedEvenMoment 2 / 6 < 3 / 25000)

/-- The centered order-21 residual annulus is unconditionally empty. -/
theorem xiCenteredOrderTwentyOneResidualAnnulusEmpty :
    XiCenteredOrderTwentyOneResidualAnnulusEmpty :=
  xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_fourthTrace_le
    normalizedPrimeArchMoment_one_lt_three_over_twentyFiveThousand.le

/-- **Unconditional closure of the centered order-21 source moment.** -/
theorem normalizedPrimeArchMoment_twenty_pos :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty
    xiCenteredOrderTwentyOneResidualAnnulusEmpty

end

end RHTower
