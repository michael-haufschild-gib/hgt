import GaloisForLFunctions.HTGeometry.EventInvolutionComplement
import GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector

/-!
# Source colligation derives the minimal paired quadratic transfer

The earlier primitive-record selector assumed that a symmetric quadratic record was odd under a
retained/created polarity. This file derives that oddness from data already present in a
source-complete event colligation.

For a source involution `A` and an event law `T`, `involutionOddPart A T` is the canonical
reciprocal transfer sector. Its transpose symmetrization is automatically symmetric. If `A` is
also transpose-symmetric, this quadratic transfer is automatically odd under `A`. In the minimal
two-channel polarity `diag(1,-1)`, every nonzero such transfer therefore lies in the unique paired
projective congruence orbit.

This is unconditional finite matrix algebra. It does not prove that a physical objective event
selects `A` or `T`, that the transfer is nonzero, that it is positive, or that it generates a
successor operational category, spacetime, gravity, or gauge forces.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

/--
Symmetric quadratic transfer extracted from the canonical odd sector of a source colligation.
-/
def sourceQuadraticTransfer
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (involutionOddPart A T + (involutionOddPart A T)ᵀ)

/-- Source quadratic transfer is symmetric by construction. -/
theorem sourceQuadraticTransfer_transpose
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ) :
    (sourceQuadraticTransfer A T)ᵀ = sourceQuadraticTransfer A T := by
  simp only [sourceQuadraticTransfer, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_transpose]
  rw [add_comm]

/--
If the source grading is a symmetric involution, its extracted symmetric transfer is
automatically source-odd. Oddness is a consequence of the colligation projection, not an
additional selector.
-/
theorem sourceQuadraticTransfer_conjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A T : Matrix n n ℂ)
    (hA : A * A = 1)
    (hAT : Aᵀ = A) :
    A * sourceQuadraticTransfer A T * A = -sourceQuadraticTransfer A T := by
  have hOdd := involutionOdd_conjugate A T hA
  have hOddT := congrArg Matrix.transpose hOdd
  simp only [Matrix.transpose_mul, Matrix.transpose_neg, hAT] at hOddT
  rw [← Matrix.mul_assoc] at hOddT
  simp only [sourceQuadraticTransfer, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]
  rw [hOdd, hOddT]
  module

/-- The minimal retained/created polarity is an involution over `ℂ`. -/
theorem recordPolarityMatrix_mul_self_complex :
    (recordPolarityMatrix : Matrix (Fin 2) (Fin 2) ℂ) *
      recordPolarityMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordPolarityMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/--
**Source-derived minimal pairing law.** Every nonzero symmetric quadratic transfer extracted from
the canonical odd sector of a minimal retained/created source colligation lies in the unique paired
projective congruence orbit.
-/
theorem sourceQuadraticTransfer_nonzero_projectivelyCongruent_pair
    (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : sourceQuadraticTransfer recordPolarityMatrix T ≠ 0) :
    ProjectivelyCongruent
      (sourceQuadraticTransfer recordPolarityMatrix T)
      pairRecordMatrix := by
  apply odd_symmetric_nonzero_projectivelyCongruent_pair
    (sourceQuadraticTransfer recordPolarityMatrix T) hQ
    (sourceQuadraticTransfer_transpose recordPolarityMatrix T)
  simpa only [recordPolarityMatrix_transpose] using
    sourceQuadraticTransfer_conjugate
      recordPolarityMatrix T recordPolarityMatrix_mul_self_complex
      recordPolarityMatrix_transpose

end GaloisForLFunctions.HTGeometry
