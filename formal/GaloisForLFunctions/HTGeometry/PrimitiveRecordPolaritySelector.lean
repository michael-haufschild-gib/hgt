import GaloisForLFunctions.HTGeometry.PrimitiveRecordQuadraticSuccessor

/-!
# Source polarity selects the paired quadratic record

The primitive-record nonselection theorem leaves two projective symmetric tensor orbits in the
smallest two-channel model: rank-one self-composition and rank-two paired composition.

This file adds one source datum already present in involution-selected event records. The
involution distinguishes retained and created directions by the polarity `diag(1,-1)`. Requiring
the first higher-record tensor to be symmetric and odd under this polarity forces both self-blocks
to vanish and leaves only the paired cross-block. Every nonzero such tensor is therefore a scalar
multiple of `pairRecordMatrix` and lies in its unique projective congruence orbit.

This is unconditional finite linear algebra. It does not prove that physical events carry this
polarity, that the odd tensor is positive or source-complete, or that higher record tensors,
spacetime, gravity, or gauge forces are selected.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

variable {K : Type*} [Field K]

/-- Polarity distinguishing retained and created primitive record directions. -/
def recordPolarityMatrix : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

@[simp]
theorem recordPolarityMatrix_transpose :
    (recordPolarityMatrix : Matrix (Fin 2) (Fin 2) K)ᵀ =
      recordPolarityMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [recordPolarityMatrix]

variable [CharZero K]

/-- A symmetric tensor odd under source polarity is exactly a scalar paired tensor. Thus source
polarity eliminates both diagonal self-composition coefficients. -/
theorem odd_symmetric_record_eq_smul_pair
    (q : Matrix (Fin 2) (Fin 2) K)
    (hsymm : qᵀ = q)
    (hodd : recordPolarityMatrixᵀ * q * recordPolarityMatrix = -q) :
    q = q 0 1 • pairRecordMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hodd
    simp only [recordPolarityMatrix_transpose, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
    simp [recordPolarityMatrix] at h00
    have h00zero : q 0 0 = 0 :=
      CharZero.eq_neg_self_iff.mp h00
    simpa [pairRecordMatrix] using h00zero
  · simp [pairRecordMatrix]
  · have hsymm := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hsymm
    simpa [pairRecordMatrix] using hsymm
  · have h11 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hodd
    simp only [recordPolarityMatrix_transpose, Matrix.mul_apply,
      Fin.sum_univ_two] at h11
    simp [recordPolarityMatrix] at h11
    have h11zero : q 1 1 = 0 :=
      CharZero.eq_neg_self_iff.mp h11
    simpa [pairRecordMatrix] using h11zero

/-- **Primitive-record polarity selection law.** Every nonzero symmetric tensor odd under the
retained/created source polarity lies in the unique paired projective congruence orbit. -/
theorem odd_symmetric_nonzero_projectivelyCongruent_pair
    (q : Matrix (Fin 2) (Fin 2) K)
    (hq : q ≠ 0)
    (hsymm : qᵀ = q)
    (hodd : recordPolarityMatrixᵀ * q * recordPolarityMatrix = -q) :
    ProjectivelyCongruent q pairRecordMatrix := by
  have hform := odd_symmetric_record_eq_smul_pair q hsymm hodd
  have hcoeff : q 0 1 ≠ 0 := by
    intro hzero
    apply hq
    rw [hform, hzero, zero_smul]
  refine ⟨1, q 0 1, by simp, hcoeff, ?_⟩
  simpa using hform

end GaloisForLFunctions.HTGeometry
