import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws under positive-cone interpolation

Positive square roots and matrix geometric means preserve strict template metrics.  Therefore the
complete local-search package from arXiv:2609.03581 survives these nonlinear changes of geometry.
At fixed dimension, interpolation changes the ellipsoid but not its leading bias or metric-unit
localization radius.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Matrix MatrixOrder

noncomputable section

/-- Continuous-functional-calculus square root of a positive template metric. -/
def PositiveTemplateMetric.sqrt {D : ℕ} (G : PositiveTemplateMetric D) :
    PositiveTemplateMetric D where
  matrix := CFC.sqrt G.matrix
  posDef := positiveMatrixSqrt_posDef G.posDef

/-- Positive-cone geometric midpoint of two template metrics. -/
def PositiveTemplateMetric.geometricMean {D : ℕ}
    (G H : PositiveTemplateMetric D) : PositiveTemplateMetric D where
  matrix := positiveMatrixGeometricMean G.matrix H.matrix
  posDef := positiveMatrixGeometricMean_posDef G.posDef H.posDef

/-- Square-root geometry satisfies all fourteen optimizer and localization laws. -/
theorem PositiveTemplateMetric.sqrt_greedyBumpLaws {D : ℕ}
    (G : PositiveTemplateMetric D) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q G.sqrt :=
  greedyBumpMetricLaws_closed Q G.sqrt

/-- Geometric-midpoint geometry satisfies all fourteen optimizer and localization laws. -/
theorem PositiveTemplateMetric.geometricMean_greedyBumpLaws {D : ℕ}
    (G H : PositiveTemplateMetric D) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (G.geometricMean H) :=
  greedyBumpMetricLaws_closed Q (G.geometricMean H)

/-- Positive-cone square roots preserve leading matched bias. -/
theorem PositiveTemplateMetric.sqrt_bias_eq {D : ℕ}
    (G : PositiveTemplateMetric D) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G.sqrt)⁻¹ * G.sqrt.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias]

/-- Positive-cone geometric interpolation preserves leading matched bias. -/
theorem PositiveTemplateMetric.geometricMean_bias_eq_left {D : ℕ}
    (G H : PositiveTemplateMetric D) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (G.geometricMean H))⁻¹ *
          (G.geometricMean H).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias]

/-- Positive-cone geometric interpolation preserves metric-unit localization radius. -/
theorem PositiveTemplateMetric.geometricMean_localizationRadius_eq_left {D : ℕ}
    (G H : PositiveTemplateMetric D) (Q : PositiveSignal) :
    Matrix.trace
        (greedyBumpLocalizationCovariance Q (G.geometricMean H) *
          (G.geometricMean H).matrix) =
      Matrix.trace (greedyBumpLocalizationCovariance Q G * G.matrix) := by
  rw [greedyBumpLocalizationCovariance_trace_mul,
    greedyBumpLocalizationCovariance_trace_mul]

end

end GaloisForLFunctions.HTGeometry
