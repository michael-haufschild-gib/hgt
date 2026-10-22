import GaloisForLFunctions.RHTower.CCM.CCMRationalResidualEvansMatrix
import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for residual Evans Grams

An injective finite residual coordinate map has a positive-definite Evans Gram.  Its doubled-real
form is a template metric for arXiv:2609.03581.  Residual output dimension controls whether the map
can identify all inputs; identified complex input rank controls the universal local-search cost.
-/

namespace GaloisForLFunctions.RHTower

open Matrix
open scoped ComplexOrder

noncomputable section

/-- Certified injective complex residual coordinate map. -/
structure GreedyBumpEvansData (m n : ℕ) where
  coordinateMap : Matrix (Fin m) (Fin n) ℂ
  injective : ∀ x : Fin n → ℂ, coordinateMap *ᵥ x = 0 → x = 0

/-- Doubled-real Evans Gram. -/
def GreedyBumpEvansData.realifiedMatrix {m n : ℕ}
    (data : GreedyBumpEvansData m n) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (GaloisForLFunctions.HTGeometry.complexMatrixRealification
      (evansGramMatrix data.coordinateMap)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Residual Evans Gram as a positive template metric. -/
def GreedyBumpEvansData.metric {m n : ℕ}
    (data : GreedyBumpEvansData m n) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (n + n) where
  matrix := data.realifiedMatrix
  posDef := (GaloisForLFunctions.HTGeometry.complexMatrixRealification_posDef
    ((posDef_evansGramMatrix_iff data.coordinateMap).mpr data.injective)).submatrix
      finSumFinEquiv.symm.injective

/-- Every injective Evans residual packet satisfies the complete local-search package. -/
theorem GreedyBumpEvansData.laws {m n : ℕ}
    (data : GreedyBumpEvansData m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- `n` identifiable complex input coordinates contribute exact bias `n / Q`. -/
theorem GreedyBumpEvansData.bias {m n : ℕ}
    (data : GreedyBumpEvansData m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      (n : ℝ) / (Q : ℝ) := by
  rw [GaloisForLFunctions.HTGeometry.greedyBump_matched_bias]
  push_cast
  field_simp [ne_of_gt Q.property]
  ring

/-- Metric-unit localization radius is `2n / Q²`. -/
theorem GreedyBumpEvansData.localizationRadius {m n : ℕ}
    (data : GreedyBumpEvansData m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    Matrix.trace
        (GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance Q data.metric *
          data.metric.matrix) =
      ((n + n : ℕ) : ℝ) / (Q : ℝ) ^ (2 : ℕ) :=
  GaloisForLFunctions.HTGeometry.greedyBumpLocalizationCovariance_trace_mul Q data.metric

end

end GaloisForLFunctions.RHTower
