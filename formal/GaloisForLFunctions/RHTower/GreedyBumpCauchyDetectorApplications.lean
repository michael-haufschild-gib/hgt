import GaloisForLFunctions.RHTower.BaezDuarteDetectorIndependence
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for Hardy Cauchy detector banks

Distinct nodes in the complex right half-plane give a strictly positive Hardy Cauchy Gram.  Its
doubled-real form is a template metric for arXiv:2609.03581, so detector location controls geometry
while detector count controls leading profiling bias and metric-unit localization.
-/

namespace RHTower

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Certified distinct right-half-plane detector nodes. -/
structure GreedyBumpCauchyDetectorData (N : ℕ) where
  node : Fin N → ℂ
  node_right : ∀ i, 0 < (node i).re
  node_injective : Function.Injective node

/-- Doubled-real Hardy Cauchy Gram. -/
def GreedyBumpCauchyDetectorData.realifiedMatrix {N : ℕ}
    (data : GreedyBumpCauchyDetectorData N) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (rightHalfPlaneHardyCauchyGram data.node)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Hardy Cauchy detector Gram as a positive template metric. -/
def GreedyBumpCauchyDetectorData.metric {N : ℕ}
    (data : GreedyBumpCauchyDetectorData N) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (rightHalfPlaneHardyCauchyGram_posDef data.node data.node_right
      data.node_injective)).submatrix finSumFinEquiv.symm.injective

/-- Every strict Cauchy detector bank satisfies the complete local-search package. -/
theorem GreedyBumpCauchyDetectorData.laws {N : ℕ}
    (data : GreedyBumpCauchyDetectorData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- `N` complex Cauchy detectors contribute exact leading bias `N / Q`. -/
theorem GreedyBumpCauchyDetectorData.bias {N : ℕ}
    (data : GreedyBumpCauchyDetectorData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      (N : ℝ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric-unit localization radius is `2N / Q²`. -/
theorem GreedyBumpCauchyDetectorData.localizationRadius {N : ℕ}
    (data : GreedyBumpCauchyDetectorData N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      ((N + N : ℕ) : ℝ) / (Q : ℝ) ^ 2 :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end RHTower
