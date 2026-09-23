import GaloisForLFunctions.HilbertMetric.PremiseWitnesses
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for separated Gaussian coherent packets

A finite point configuration separated by one coordinate has a strictly positive exponential
inner Gram at every positive bandwidth.  This realizes the configuration as a template metric for
arXiv:2609.03581.  Ambient coordinates and bandwidth shape the metric, while point count alone
sets leading bias and metric-unit localization.
-/

namespace GaloisForLFunctions.HilbertMetric

open Matrix

noncomputable section

/-- Certified finite configuration with one separating coordinate and positive bandwidth. -/
structure GreedyBumpGaussianCoherentData (d n : ℕ) where
  point : Fin n → Fin d → ℝ
  separatingCoordinate : Fin d
  coordinate_injective : Function.Injective fun i => point i separatingCoordinate
  bandwidth : GaloisForLFunctions.HTGeometry.PositiveSignal

/-- Exponential inner Gram of the separated point configuration. -/
def GreedyBumpGaussianCoherentData.metric {d n : ℕ}
    (data : GreedyBumpGaussianCoherentData d n) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric n where
  matrix := finiteExponentialInnerGram data.point data.bandwidth
  posDef := finiteExponentialInnerGram_posDef_of_coordinate_injective data.point
    data.separatingCoordinate data.coordinate_injective data.bandwidth.property

/-- The metric is exactly a Gaussian coherent Gram after square-root bandwidth scaling. -/
theorem GreedyBumpGaussianCoherentData.metric_eq_gaussianCoherentGram {d n : ℕ}
    (data : GreedyBumpGaussianCoherentData d n) :
    data.metric.matrix =
      gaussianCoherentGram
        (fun i a => Real.sqrt (data.bandwidth : ℝ) * data.point i a) :=
  finiteExponentialInnerGram_eq_gaussianCoherentGram data.point data.bandwidth.property.le

/-- Every separated Gaussian coherent packet satisfies the complete local-search package. -/
theorem GreedyBumpGaussianCoherentData.laws {d n : ℕ}
    (data : GreedyBumpGaussianCoherentData d n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- A separated `n`-point coherent packet contributes exact bias `n / (2Q)`. -/
theorem GreedyBumpGaussianCoherentData.bias {d n : ℕ}
    (data : GreedyBumpGaussianCoherentData d n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      (n : ℝ) / (2 * (Q : ℝ)) :=
  GaloisForLFunctions.HTGeometry.greedyBump_matched_bias Q data.metric

/-- Metric-unit localization radius is `n / Q²`. -/
theorem GreedyBumpGaussianCoherentData.localizationRadius {d n : ℕ}
    (data : GreedyBumpGaussianCoherentData d n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      (n : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end GaloisForLFunctions.HilbertMetric
