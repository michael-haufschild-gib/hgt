import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallAllOrderMalgrangeOrientation

/-!
# Wold-coordinate third/fifth Malgrange separation

The complete source-horizontal Wold profile begins with the fixed odd coefficients
`-z^3 / 9 - z^5 / 150`. Treating it as a source-defined spectral coordinate for the cold
prime/Gamma wall preserves the calibrated first and quadratic jets. Cubic calibration then forces
the fifth coordinate contribution to be

`(6 / 5 + 5 * m₀²) * (m₂ - m₀³ / 4)`.

The actual fifth cold Malgrange target is `12 * (m₄ - m₀⁵ / 16)`. This module proves their strict
separation from source moment bounds alone. The remaining carrier-to-coordinate pullback identity
is deliberately not claimed here; this is its exact fifth-jet obstruction once that identity is
established.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Candidate fifth logarithmic-jet correction forced by the cubic Wold-coordinate calculation. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallWoldCoordinateFifthPrediction : ℝ :=
  ((6 / 5 : ℝ) + 5 * normalizedPrimeArchMoment 0 ^ 2) *
    (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4)

/-- Literal fifth cold Malgrange correction after forced first-jet normalization. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFifthMalgrangeTarget : ℝ :=
  12 * (normalizedPrimeArchMoment 4 - normalizedPrimeArchMoment 0 ^ 5 / 16)

/-- **Wold-coordinate third/fifth separation.** The candidate fifth correction forced by cubic
Wold calibration is strictly more negative than the literal completed prime--archimedean fifth
Malgrange target. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallWoldCoordinateFifthPrediction_lt_target :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallWoldCoordinateFifthPrediction <
      routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFifthMalgrangeTarget := by
  have hm0low := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hm0high := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  have hm0pos : 0 < normalizedPrimeArchMoment 0 := by
    nlinarith
  have hmass := xiShiftAbsoluteMass_one_lt_secondMomentBudget
  have hm2abs := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 1 1
  have hm2le : normalizedPrimeArchMoment 2 ≤
      (1 / 150 : ℝ) * xiShiftAbsoluteMass 1 := by
    norm_num at hm2abs ⊢
    exact (le_abs_self _).trans hm2abs
  have hm2upper : normalizedPrimeArchMoment 2 <
      ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) / 150 := by
    nlinarith
  have hm4abs := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 1 3
  have hm4lower :
      -(((42 / 41 : ℝ) * (17 / 200000 : ℝ)) / 150 ^ 3) <
        normalizedPrimeArchMoment 4 := by
    have hscale : 0 < (1 / 150 : ℝ) ^ 3 := by positivity
    have hbound : (1 / 150 : ℝ) ^ 3 * xiShiftAbsoluteMass 1 <
        (1 / 150 : ℝ) ^ 3 * ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) :=
      mul_lt_mul_of_pos_left hmass hscale
    norm_num at hm4abs ⊢
    nlinarith [neg_abs_le (normalizedPrimeArchMoment 4)]
  have hm0cube : (1 / 25 : ℝ) ^ 3 < normalizedPrimeArchMoment 0 ^ 3 :=
    pow_lt_pow_left₀ hm0low (by norm_num) (by norm_num)
  have hm0fifth : normalizedPrimeArchMoment 0 ^ 5 <
      (29 / 625 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hm0high hm0pos.le (by norm_num)
  have hdelta : normalizedPrimeArchMoment 2 -
      normalizedPrimeArchMoment 0 ^ 3 / 4 < -(1 / 100000 : ℝ) := by
    have hrat :
        ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) / 150 -
          (1 / 25 : ℝ) ^ 3 / 4 < -(1 / 100000 : ℝ) := by norm_num
    nlinarith
  have htarget : -(1 / 1000000 : ℝ) <
      12 * (normalizedPrimeArchMoment 4 - normalizedPrimeArchMoment 0 ^ 5 / 16) := by
    have hrat : -(1 / 1000000 : ℝ) <
        12 * (-(((42 / 41 : ℝ) * (17 / 200000 : ℝ)) / 150 ^ 3) -
          (29 / 625 : ℝ) ^ 5 / 16) := by norm_num
    nlinarith
  have hfactor : (6 / 5 : ℝ) <
      (6 / 5 : ℝ) + 5 * normalizedPrimeArchMoment 0 ^ 2 := by
    have hsq : 0 < normalizedPrimeArchMoment 0 ^ 2 := sq_pos_of_pos hm0pos
    nlinarith
  have hfactorPos : 0 <
      (6 / 5 : ℝ) + 5 * normalizedPrimeArchMoment 0 ^ 2 := by positivity
  unfold routePPrimitiveGammaJuliaStokesPrimeGammaWallWoldCoordinateFifthPrediction
    routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFifthMalgrangeTarget
  calc
    ((6 / 5 : ℝ) + 5 * normalizedPrimeArchMoment 0 ^ 2) *
        (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) <
        ((6 / 5 : ℝ) + 5 * normalizedPrimeArchMoment 0 ^ 2) *
          (-(1 / 100000 : ℝ)) :=
      mul_lt_mul_of_pos_left hdelta hfactorPos
    _ < (6 / 5 : ℝ) * (-(1 / 100000 : ℝ)) :=
      mul_lt_mul_of_neg_right hfactor (by norm_num)
    _ < -(1 / 1000000 : ℝ) := by norm_num
    _ < 12 * (normalizedPrimeArchMoment 4 - normalizedPrimeArchMoment 0 ^ 5 / 16) := htarget

end

end RHTower
