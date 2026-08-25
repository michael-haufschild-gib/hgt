import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuarticMalgrangePositiveOrientation
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCanonicalNegativeCubicOrientationLanding
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import GaloisForLFunctions.RHTower.TwoPrimeKummerClockSeparation

/-!
# Raw cubic Euler/Wold magnitude overshoots the Xi Malgrange target

Same-chamber orientation does not suffice for a coefficient-faithful irregular-RH landing.  The
raw summable Euler/Gamma--Wold cubic magnitude already exceeds `2000` times the canonical wall--Xi
cubic Malgrange magnitude.  Thus identity-scale transport is impossible, while any surviving
landing mechanism must supply a genuine source-derived contraction.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The canonical wall--Xi cubic Malgrange magnitude has an exact rational upper bound. -/
theorem neg_normalizedPrimeArchMoment_two_sub_zero_cube_div_four_lt_one_div_tenThousand :
    -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) <
      (1 / 10000 : ℝ) := by
  let A := thetaCuspNormalizedEvenMoment 1
  let B := thetaCuspNormalizedEvenMoment 2
  let C := thetaCuspNormalizedEvenMoment 3
  have h0 := thetaCuspRawEvenMoment_zero_pos
  have hApos : 0 < A := by
    dsimp only [A, thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 1) h0
  have hC : 0 ≤ C := by
    dsimp only [C, thetaCuspNormalizedEvenMoment]
    exact div_nonneg (thetaCuspRawEvenMoment_nonneg 3) h0.le
  have hstrict := thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq
  have hBA : B < 6 * A ^ 2 := by
    dsimp only [A, B, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  have hAupper : A < 1 / 20 := by
    dsimp only [A]
    rw [← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    nlinarith [normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive]
  have hAB : A * B < 6 * A ^ 3 := by
    have h := mul_lt_mul_of_pos_left hBA hApos
    nlinarith
  have hApow : A ^ 3 < (1 / 20 : ℝ) ^ 3 := by
    gcongr
  rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  dsimp only [A, B, C] at *
  nlinarith

/-- Prime `2` gives an exact closed-form atom in the raw Euler/Gamma--Wold defect. -/
theorem sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_eq :
    sourceHorizontalEulerGammaWoldCubicNaturalDefect 2 =
      (95 / 16 : ℝ) * Real.log 2 ^ 3 := by
  rw [sourceHorizontalEulerGammaWoldCubicNaturalDefect,
    dif_pos Nat.prime_two, sourceHorizontalEulerGammaWoldCubicDefect_eq]
  norm_num
  ring

/-- The first prime alone forces a uniform rational lower bound on the complete raw source
magnitude. -/
theorem one_div_five_lt_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect :
    (1 / 5 : ℝ) <
      ∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
  have hterm : sourceHorizontalEulerGammaWoldCubicNaturalDefect 2 ≤
      ∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
    have hsum := summable_sourceHorizontalEulerGammaWoldCubicNaturalDefect
    simpa using hsum.sum_le_tsum {2}
      (fun n hn => sourceHorizontalEulerGammaWoldCubicNaturalDefect_nonneg n)
  have hlog := GaloisForLFunctions.RHTower.one_third_lt_log_two
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfactor : 0 <
      Real.log 2 ^ 2 + Real.log 2 * (1 / 3 : ℝ) + (1 / 3 : ℝ) ^ 2 := by
    positivity
  have hcube : (1 / 3 : ℝ) ^ 3 < Real.log 2 ^ 3 := by
    nlinarith [mul_pos (sub_pos.mpr hlog) hfactor]
  rw [sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_eq] at hterm
  nlinarith

/-- Quantitative scale aperture: raw source magnitude exceeds `2000` times the canonical Xi cubic
Malgrange magnitude. -/
theorem twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource :
    2000 * (-(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4)) <
      ∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n := by
  nlinarith
    [neg_normalizedPrimeArchMoment_two_sub_zero_cube_div_four_lt_one_div_tenThousand,
      one_div_five_lt_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect]

/-- Signed form of the no-go: the raw renormalized Euler/Gamma--Wold current is strictly more
negative than the wall--Xi cubic Malgrange residual, so identity-scale landing is impossible. -/
theorem neg_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect_lt_xiCubicResidual :
    -(∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n) <
      normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4 := by
  have htarget := normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
  have hgap := twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource
  nlinarith

/-- Complete raw-magnitude obstruction and surviving factor-`2000` contraction aperture. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot :
    0 < -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) ∧
      -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) <
        (1 / 10000 : ℝ) ∧
      (1 / 5 : ℝ) <
        ∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n ∧
      2000 * (-(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4)) <
        ∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n ∧
      -(∑' n : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect n) <
        normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4 := by
  exact ⟨neg_pos.mpr normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg,
    neg_normalizedPrimeArchMoment_two_sub_zero_cube_div_four_lt_one_div_tenThousand,
    one_div_five_lt_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect,
    twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource,
    neg_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect_lt_xiCubicResidual⟩

end

end RHTower
