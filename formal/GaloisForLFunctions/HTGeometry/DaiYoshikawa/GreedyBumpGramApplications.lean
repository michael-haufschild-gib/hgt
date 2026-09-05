import GaloisForLFunctions.HTGeometry.DaiYoshikawa.GramPositiveDefinite
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for linearly independent Hilbert families

Every finite linearly independent family in a complex Hilbert space has a positive-definite Gram
matrix.  Doubled-real conversion therefore makes every such certified family a receiver for the
local-search laws of arXiv:2609.03581.  The laws see complex feature rank, not the ambient Hilbert
space or the semantic origin of the vectors.
-/

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open Matrix
open scoped ComplexOrder

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Certified finite linearly independent complex Hilbert family. -/
structure GreedyBumpHilbertGramData (N : ℕ) where
  vector : Fin N → E
  independent : LinearIndependent ℂ vector

/-- Doubled-real Gram matrix of the Hilbert family. -/
def GreedyBumpHilbertGramData.realifiedMatrix {N : ℕ}
    (data : GreedyBumpHilbertGramData (E := E) N) :
    Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (GaloisForLFunctions.HTGeometry.gramMatrix data.vector)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Hilbert Gram as a positive template metric. -/
def GreedyBumpHilbertGramData.metric {N : ℕ}
    (data : GreedyBumpHilbertGramData (E := E) N) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (N + N) where
  matrix := data.realifiedMatrix
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    (gramMatrix_posDef_of_linearIndependent data.independent)).submatrix
      finSumFinEquiv.symm.injective

/-- Every independent Hilbert family satisfies the complete local-search package. -/
theorem GreedyBumpHilbertGramData.laws {N : ℕ}
    (data : GreedyBumpHilbertGramData (E := E) N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- `N` independent complex Hilbert features contribute exact bias `N / Q`. -/
theorem GreedyBumpHilbertGramData.bias {N : ℕ}
    (data : GreedyBumpHilbertGramData (E := E) N)
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
theorem GreedyBumpHilbertGramData.localizationRadius {N : ℕ}
    (data : GreedyBumpHilbertGramData (E := E) N)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      ((N + N : ℕ) : ℝ) / (Q : ℝ) ^ 2 :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
