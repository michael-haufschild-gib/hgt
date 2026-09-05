import GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralHankel
import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry

/-!
# Greedy-bump laws for matrix-valued spectral Hankel blocks

Jointly identifiable clock/channel spectral features give a strictly positive block Hankel metric.
After finite-product reindexing, arXiv:2609.03581 applies in dimension `clockDepth * channelCount`.
The same independence certificate forces this dimension not to exceed spectral-line capacity.
-/

namespace HTGeometry

open Matrix

noncomputable section

/-- Certified identifiable matrix-valued finite spectral packet. -/
structure GreedyBumpMatrixSpectralData (d m n : ℕ) where
  mass : Fin d → ℝ
  node : Fin d → ℝ
  coupling : Fin d → Fin m → ℝ
  mass_nonnegative : ∀ r, 0 ≤ mass r
  features_independent : LinearIndependent ℝ
    (finiteMatrixSpectralFeature mass node coupling :
      Fin n × Fin m → EuclideanSpace ℝ (Fin d))

/-- Reindexed block Hankel matrix on `Fin (n * m)`. -/
def GreedyBumpMatrixSpectralData.matrix {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n) :
    Matrix (Fin (n * m)) (Fin (n * m)) ℝ :=
  (finiteMatrixSpectralBlockHankel data.mass data.node data.coupling n).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- Identifiable spectral block as a positive template metric. -/
def GreedyBumpMatrixSpectralData.metric {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n) :
    GaloisForLFunctions.HTGeometry.PositiveTemplateMetric (n * m) where
  matrix := data.matrix
  posDef := ((finiteMatrixSpectralBlockHankel_posDef_iff_linearIndependent
    data.mass data.node data.coupling data.mass_nonnegative n).mpr
      data.features_independent).submatrix finProdFinEquiv.symm.injective

/-- Identifiability forces clock-channel dimension below spectral-line capacity. -/
theorem GreedyBumpMatrixSpectralData.dimension_le_spectralLines {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n) : n * m ≤ d := by
  have h := data.features_independent.fintype_card_le_finrank
  simpa only [Fintype.card_prod, Fintype.card_fin,
    finrank_euclideanSpace_fin] using h

/-- Every identifiable matrix spectral block satisfies the complete local-search package. -/
theorem GreedyBumpMatrixSpectralData.laws {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    GaloisForLFunctions.HTGeometry.GreedyBumpMetricLaws Q data.metric :=
  GaloisForLFunctions.HTGeometry.greedyBumpMetricLaws_closed Q data.metric

/-- Leading bias counts all clock-channel coordinates. -/
theorem GreedyBumpMatrixSpectralData.bias {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) =
      ((n * m : ℕ) : ℝ) / (2 * (Q : ℝ)) :=
  GaloisForLFunctions.HTGeometry.greedyBump_matched_bias Q data.metric

/-- Spectral capacity bounds bias by `d / (2Q)`. -/
theorem GreedyBumpMatrixSpectralData.bias_le_spectralCapacity {d m n : ℕ}
    (data : GreedyBumpMatrixSpectralData d m n)
    (Q : GaloisForLFunctions.HTGeometry.PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((GaloisForLFunctions.HTGeometry.greedyBumpHessian Q data.metric)⁻¹ *
          data.metric.matrix) ≤
      (d : ℝ) / (2 * (Q : ℝ)) := by
  rw [data.bias]
  have hdim : ((n * m : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast data.dimension_le_spectralLines
  exact div_le_div_of_nonneg_right hdim
    (mul_nonneg (by norm_num) (le_of_lt Q.property))

end

end HTGeometry
