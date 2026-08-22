import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallFirstJetInvariant
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion

/-!
# P-G105: canonical theta-jet separation at the exponential SP-E wall

The fixed source scaling of the exponential signed-permutation wall has quadratic signed-product
jet `-16 / 35`.  The completed theta/Xi central normalization has quadratic jet
`-thetaCuspNormalizedEvenMoment 1 / 2`.  Existing source bounds put the latter strictly below
`29 / 1250`, so these jets cannot agree at the canonical scale.

This is a no-go only for the fixed canonical scaling.  It leaves open a separately source-derived
scale law or correction, which must be supplied without fitting Xi data.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-- The completed theta curvature is strictly below the value required by canonical SP-E wall
quadratic-jet matching. -/
theorem thetaCuspNormalizedEvenMoment_one_lt_wallSignedSquareCalibration :
    thetaCuspNormalizedEvenMoment 1 < 32 / 35 := by
  rw [← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  exact normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive.trans (by norm_num)

/-- The canonical completed-theta curvature cannot equal the fixed SP-E wall calibration. -/
theorem thetaCuspNormalizedEvenMoment_one_ne_wallSignedSquareCalibration :
    thetaCuspNormalizedEvenMoment 1 ≠ 32 / 35 :=
  ne_of_lt thetaCuspNormalizedEvenMoment_one_lt_wallSignedSquareCalibration

/-- The fixed canonical SP-E wall product jet is not the central completed-theta/Xi quadratic
jet.  Thus any divisor landing must exhibit a genuinely source-derived rescaling or correction. -/
theorem routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_ne_thetaCanonical :
    2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 2 -
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) 1 ^ 2 ≠
        -((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_exp]
  intro h
  have hreal := congrArg Complex.re h
  norm_num at hreal
  apply thetaCuspNormalizedEvenMoment_one_ne_wallSignedSquareCalibration
  linarith

end

end RHTower
