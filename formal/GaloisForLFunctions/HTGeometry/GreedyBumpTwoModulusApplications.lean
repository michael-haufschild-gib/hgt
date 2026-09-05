import GaloisForLFunctions.HTGeometry.TwoModulusLogHessian
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for two-modulus flux geometry

The positive flux log-Hessian supplies a literal two-coordinate template metric.  Applying the
local profiling identities of arXiv:2609.03581 gives a two-degree profile gain, `1/Q` amplitude
bias, `Q²` trials-volume exponent, and `2/Q²` localization radius.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive two-radion flux Hessian as a template metric. -/
def greedyBumpTwoModulusFluxMetric
    (logB logQ logM logN x y : ℝ) : PositiveTemplateMetric 2 where
  matrix := twoModulusFluxLogHessian logB logQ (Real.exp logM) (Real.exp logN) x y
  posDef := twoModulusFluxLogHessian_exp_posDef logB logQ logM logN x y

/-- All fourteen local-search laws hold for the two-modulus flux geometry. -/
theorem greedyBumpTwoModulusFlux_laws
    (logB logQ logM logN x y : ℝ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q
      (greedyBumpTwoModulusFluxMetric logB logQ logM logN x y) :=
  greedyBumpMetricLaws_closed Q _

/-- Profiling the two logarithmic radii produces leading bias `1/Q`. -/
theorem greedyBumpTwoModulusFlux_bias
    (logB logQ logM logN x y : ℝ) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q
          (greedyBumpTwoModulusFluxMetric logB logQ logM logN x y))⁻¹ *
          (greedyBumpTwoModulusFluxMetric logB logQ logM logN x y).matrix) =
      1 / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  norm_num
  field_simp [ne_of_gt Q.property]

/-- Metric-unit localization radius of both moduli is `2/Q²`. -/
theorem greedyBumpTwoModulusFlux_localizationRadius
    (logB logQ logM logN x y : ℝ) (Q : PositiveSignal) :
    Matrix.trace
        (greedyBumpLocalizationCovariance Q
            (greedyBumpTwoModulusFluxMetric logB logQ logM logN x y) *
          (greedyBumpTwoModulusFluxMetric logB logQ logM logN x y).matrix) =
      2 / (Q : ℝ) ^ 2 := by
  exact greedyBumpLocalizationCovariance_trace_mul Q _

/-- The two-modulus trials-factor logarithm has slope `2/Q`. -/
theorem greedyBumpTwoModulusFlux_trialsSlope
    (logB logQ logM logN x y : ℝ) (K Q : PositiveSignal) :
    HasDerivAt (greedyBumpLogTrialsFactor 2 K) (2 / (Q : ℝ)) (Q : ℝ) :=
  (greedyBumpTwoModulusFlux_laws logB logQ logM logN x y Q).logTrialsSlope K

end

end GaloisForLFunctions.HTGeometry
