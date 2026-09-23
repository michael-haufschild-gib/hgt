import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for prescribed innovation clocks

Every strictly positive finite innovation packet has a positive-definite inverse-Cholesky Gram.
After doubled-real conversion it is a template metric for arXiv:2609.03581.  Innovation sizes set
the coordinate geometry, while packet length alone sets leading bias and metric-unit localization.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Certified strictly positive innovation amplitudes. -/
structure GreedyBumpInnovationData (N : ℕ) where
  innovation : Fin N → ℝ
  innovation_pos : ∀ i, 0 < innovation i

/-- Doubled-real inverse-Cholesky innovation Gram. -/
def GreedyBumpInnovationData.realifiedMatrix {N : ℕ}
    (data : GreedyBumpInnovationData N) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  (complexMatrixRealification
      (prescribedPositiveInnovationGram data.innovation)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Prescribed innovation clock as a positive template metric. -/
def GreedyBumpInnovationData.metric {N : ℕ}
    (data : GreedyBumpInnovationData N) : PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (complexMatrixRealification_posDef
    (prescribedPositiveInnovationGram_posDef data.innovation
      data.innovation_pos)).submatrix finSumFinEquiv.symm.injective

/-- Every positive innovation packet satisfies the complete local-search law package. -/
theorem GreedyBumpInnovationData.laws {N : ℕ}
    (data : GreedyBumpInnovationData N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q data.metric :=
  greedyBumpMetricLaws_closed Q data.metric

/-- `N` complex innovation channels contribute exact leading bias `N / Q`. -/
theorem GreedyBumpInnovationData.bias {N : ℕ}
    (data : GreedyBumpInnovationData N) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q data.metric)⁻¹ * data.metric.matrix) =
      (N : ℝ) / (Q : ℝ) := by
  rw [greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric-unit localization radius is `2N / Q²`, independent of innovation amplitudes. -/
theorem GreedyBumpInnovationData.localizationRadius {N : ℕ}
    (data : GreedyBumpInnovationData N) (Q : PositiveSignal) :
    Matrix.trace
        (greedyBumpLocalizationCovariance Q data.metric * data.metric.matrix) =
      ((N + N : ℕ) : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end GaloisForLFunctions.HTGeometry
