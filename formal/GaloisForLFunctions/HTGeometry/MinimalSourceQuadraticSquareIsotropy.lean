import GaloisForLFunctions.HTGeometry.SourceQuadraticTransferSelector

/-!
# The minimal source-selected quadratic square is isotropic

The minimal retained/created polarity forces every symmetric source quadratic transfer to be a
scalar multiple of the paired matrix. This file computes its positive reciprocal square: it is the
modulus-square of that scalar times the identity.

Thus the minimal two-channel selector fixes an amplitude direction but cannot produce anisotropic
geometry, distinct force sectors, or relative couplings. Projective congruence also discards the
only remaining scalar, while the positive square depends on it. Physical weighting therefore
requires source-calibrated normalization or higher record structure.

These are unconditional symbolic matrix identities, not new mathematics or physics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

/-- The paired quadratic record is self-adjoint over `ℂ`. -/
theorem pairRecordMatrix_conjTranspose_complex :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      pairRecordMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairRecordMatrix]

/-- The paired quadratic record is an involution over `ℂ`. -/
theorem pairRecordMatrix_mul_self_complex :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) ℂ) *
      pairRecordMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The reciprocal square of a scalar paired transfer is isotropic. -/
theorem smul_pairRecord_reciprocalSquare_isotropic
    (b : ℂ) :
    (b • (pairRecordMatrix : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        (b • pairRecordMatrix) =
      (star b * b) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.conjTranspose_smul, pairRecordMatrix_conjTranspose_complex,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    pairRecordMatrix_mul_self_complex]

/--
**Minimal source-square isotropy law.** Every source-derived symmetric quadratic transfer in the
minimal retained/created model has a scalar positive square.
-/
theorem minimalSourceQuadratic_reciprocalSquare_isotropic
    (T : Matrix (Fin 2) (Fin 2) ℂ) :
    let Q := sourceQuadraticTransfer recordPolarityMatrix T
    Qᴴ * Q =
      (star (Q 0 1) * Q 0 1) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  dsimp only
  have hform := odd_symmetric_record_eq_smul_pair
    (sourceQuadraticTransfer recordPolarityMatrix T)
    (sourceQuadraticTransfer_transpose recordPolarityMatrix T)
    (by
      simpa only [recordPolarityMatrix_transpose] using
        sourceQuadraticTransfer_conjugate
          recordPolarityMatrix T recordPolarityMatrix_mul_self_complex
          recordPolarityMatrix_transpose)
  rw [hform]
  simpa [pairRecordMatrix] using
    smul_pairRecord_reciprocalSquare_isotropic
      (sourceQuadraticTransfer recordPolarityMatrix T 0 1)

end GaloisForLFunctions.HTGeometry
