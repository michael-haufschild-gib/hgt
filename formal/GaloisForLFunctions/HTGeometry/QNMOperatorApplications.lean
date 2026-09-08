import GaloisForLFunctions.HilbertMetric.QNMMatrixBackwardError
import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBranchRCLike

/-!
# QNMOperatorApplications

The optical QNM perturbation characterization gives exact smallest errors
for source chiral matrices and corrects the eigen-equation component of the
corpus eigenpair continuation residual while retaining its normalization component.
-/

noncomputable section
open GaloisForLFunctions.HilbertMetric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry

theorem sourceEscapingChiralOperator_qnmBackwardError
    {m : Type*} [Fintype m] [DecidableEq m] (k : ℕ) (C : Matrix m m ℂ)
    (z : ℂ) (v : EuclideanSpace ℂ (m ⊕ m)) :
    IsLeast {r : ℝ | ∃ D : Matrix (m ⊕ m) (m ⊕ m) ℂ,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m ⊕ m)
        (sourceEscapingChiralOperator k C + D) v = z • v ∧ ‖D‖ = r}
      (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m ⊕ m)
        (sourceEscapingChiralOperator k C) v - z • v‖ / ‖v‖) := by
  simpa using qnmMatrixBackwardError_isLeast (sourceEscapingChiralOperator k C) 1 z v

theorem eigenResidualRC_qnmCorrection
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A : ℝ → E →L[𝕜] E) (reference : E) (q : ℝ × (E × 𝕜)) :
    eigenResidualRC
      (fun t => A t + qnmBackwardCorrection (A q.1) 1 q.2.2 q.2.1)
      reference q = (0, inner 𝕜 reference q.2.1 - 1) := by
  unfold eigenResidualRC
  congr 1
  have h := qnmBackwardCorrection_exact (A q.1) 1 q.2.2 q.2.1
  simpa using sub_eq_zero.mpr h

theorem eigenResidualRC_qnmCorrection_norm
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A : ℝ → E →L[𝕜] E) (reference : E) (q : ℝ × (E × 𝕜)) :
    ‖qnmBackwardCorrection (A q.1) 1 q.2.2 q.2.1‖ =
      ‖(eigenResidualRC A reference q).1‖ / ‖q.2.1‖ := by
  simpa [eigenResidualRC] using norm_qnmBackwardCorrection (A q.1) 1 q.2.2 q.2.1

end GaloisForLFunctions.HTGeometry
