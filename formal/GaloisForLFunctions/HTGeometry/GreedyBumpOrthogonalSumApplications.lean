import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSum
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for orthogonal metric sums

Independent positive metric blocks assemble by orthogonal sum.  The local-search laws of
arXiv:2609.03581 then make both leading matched bias and metric-unit localization radius additive
across the blocks.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- Orthogonal sum of two positive template metrics, reindexed by `Fin (D + E)`. -/
def PositiveTemplateMetric.orthogonalSum {D E : ℕ}
    (G : PositiveTemplateMetric D) (H : PositiveTemplateMetric E) :
    PositiveTemplateMetric (D + E) where
  matrix := (matrixOrthogonalSum G.matrix H.matrix).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  posDef := (matrixOrthogonalSum_posDef G.posDef H.posDef).submatrix
    finSumFinEquiv.symm.injective

/-- Every orthogonally assembled search geometry satisfies the complete paper law package. -/
theorem PositiveTemplateMetric.orthogonalSum_greedyBumpLaws {D E : ℕ}
    (G : PositiveTemplateMetric D) (H : PositiveTemplateMetric E)
    (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (G.orthogonalSum H) :=
  greedyBumpMetricLaws_closed Q (G.orthogonalSum H)

/-- Matched bias of independent blocks is exactly additive. -/
theorem PositiveTemplateMetric.orthogonalSum_bias_additive {D E : ℕ}
    (G : PositiveTemplateMetric D) (H : PositiveTemplateMetric E)
    (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (G.orthogonalSum H))⁻¹ *
          (G.orthogonalSum H).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
          ((greedyBumpHessian Q G)⁻¹ * G.matrix) +
        (1 / 2 : ℝ) * Matrix.trace
          ((greedyBumpHessian Q H)⁻¹ * H.matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias,
    greedyBump_matched_bias]
  push_cast
  ring

/-- Metric-unit localization radius of independent blocks is exactly additive. -/
theorem PositiveTemplateMetric.orthogonalSum_localizationRadius_additive {D E : ℕ}
    (G : PositiveTemplateMetric D) (H : PositiveTemplateMetric E)
    (Q : PositiveSignal) :
    Matrix.trace
        (greedyBumpLocalizationCovariance Q (G.orthogonalSum H) *
          (G.orthogonalSum H).matrix) =
      Matrix.trace (greedyBumpLocalizationCovariance Q G * G.matrix) +
        Matrix.trace (greedyBumpLocalizationCovariance Q H * H.matrix) := by
  rw [greedyBumpLocalizationCovariance_trace_mul,
    greedyBumpLocalizationCovariance_trace_mul,
    greedyBumpLocalizationCovariance_trace_mul]
  push_cast
  ring

/-! ## Finite homogeneous block families -/

/-- Block diagonal sum of `K` positive `D`-dimensional metrics. -/
def PositiveTemplateMetric.familyBlock {K D : ℕ}
    (G : Fin K → PositiveTemplateMetric D) : PositiveTemplateMetric (K * D) where
  matrix := (matrixFamilyBlockDiagonal fun k => (G k).matrix).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm
  posDef := (matrixFamilyBlockDiagonal_posDef fun k => (G k).posDef).submatrix
    finProdFinEquiv.symm.injective

/-- Every finite independent family of metric blocks satisfies the complete paper package. -/
theorem PositiveTemplateMetric.familyBlock_greedyBumpLaws {K D : ℕ}
    (G : Fin K → PositiveTemplateMetric D) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (PositiveTemplateMetric.familyBlock G) :=
  greedyBumpMetricLaws_closed Q (PositiveTemplateMetric.familyBlock G)

/-- `K` independent `D`-direction sectors contribute exact bias `KD/(2Q)`. -/
theorem PositiveTemplateMetric.familyBlock_bias {K D : ℕ}
    (G : Fin K → PositiveTemplateMetric D) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (PositiveTemplateMetric.familyBlock G))⁻¹ *
          (PositiveTemplateMetric.familyBlock G).matrix) =
      ((K * D : ℕ) : ℝ) / (2 * (Q : ℝ)) :=
  greedyBump_matched_bias Q (PositiveTemplateMetric.familyBlock G)

/-- Finite block bias equals the sum of component biases. -/
theorem PositiveTemplateMetric.familyBlock_bias_eq_sum {K D : ℕ}
    (G : Fin K → PositiveTemplateMetric D) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (PositiveTemplateMetric.familyBlock G))⁻¹ *
          (PositiveTemplateMetric.familyBlock G).matrix) =
      ∑ k, (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (G k))⁻¹ * (G k).matrix) := by
  rw [PositiveTemplateMetric.familyBlock_bias]
  simp_rw [greedyBump_matched_bias]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
