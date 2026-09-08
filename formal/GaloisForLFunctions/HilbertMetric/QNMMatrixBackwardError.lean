import GaloisForLFunctions.HilbertMetric.QNMBackwardError
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# QNMMatrixBackwardError

The exact operator correction transports isometrically to finite matrices.
This is the smallest matrix perturbation behind equations (31)--(32) of
Al Sheikh--Jaramillo, arXiv:2607.25133.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HilbertMetric
variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

def qnmMatrixBackwardCorrection (A B : Matrix ι ι 𝕜) (z : 𝕜)
    (v : EuclideanSpace 𝕜 ι) : Matrix ι ι 𝕜 :=
  (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)).symm
    (qnmBackwardCorrection (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A) (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B) z v)

theorem qnmMatrixBackwardCorrection_exact (A B : Matrix ι ι 𝕜) (z : 𝕜)
    (v : EuclideanSpace 𝕜 ι) :
    Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (A + qnmMatrixBackwardCorrection A B z v) v =
      z • Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B v := by
  simpa [qnmMatrixBackwardCorrection, map_add] using
    qnmBackwardCorrection_exact (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A) (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B) z v

theorem norm_qnmMatrixBackwardCorrection (A B : Matrix ι ι 𝕜) (z : 𝕜)
    (v : EuclideanSpace 𝕜 ι) :
    ‖qnmMatrixBackwardCorrection A B z v‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A v - z • Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B v‖ / ‖v‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  simp only [qnmMatrixBackwardCorrection, StarAlgEquiv.apply_symm_apply]
  exact norm_qnmBackwardCorrection _ _ _ _

theorem qnmMatrixBackwardError_isLeast (A B : Matrix ι ι 𝕜) (z : 𝕜)
    (v : EuclideanSpace 𝕜 ι) :
    IsLeast {r : ℝ | ∃ D : Matrix ι ι 𝕜,
      Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (A + D) v = z • Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B v ∧ ‖D‖ = r}
      (‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A v - z • Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B v‖ / ‖v‖) := by
  constructor
  · exact ⟨qnmMatrixBackwardCorrection A B z v, qnmMatrixBackwardCorrection_exact A B z v,
      norm_qnmMatrixBackwardCorrection A B z v⟩
  · rintro r ⟨D, hD, rfl⟩
    have h := (qnmBackwardError_isLeast (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A)
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) B) z v).2
      ⟨Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) D, by simpa only [map_add] using hD, rfl⟩
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using h

end GaloisForLFunctions.HilbertMetric
