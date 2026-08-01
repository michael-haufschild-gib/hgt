import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Complementary blocks of inverse matrices

Two mutually inverse matrices, written in opposite block shapes, have their off-diagonal blocks
related: the lower left block of one is a determinant multiple of the lower left block of the other,
and the multiplier is the determinant of the first matrix with its two column blocks exchanged.

The mechanism is a single auxiliary matrix, built from the second matrix by replacing one of its
column blocks by the identity.  Multiplying the first matrix by it produces a block triangular
matrix on both sides of the equation, and the two block triangular determinants are the two blocks
in question.

This is the block form of the classical relation between complementary minors of a matrix and of its
inverse.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommRing R]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommRing R] in
/-- **Exchanging the two column blocks.** -/
theorem submatrix_sumComm_fromBlocks (A : Matrix α β R) (B : Matrix α α R)
    (C : Matrix β β R) (D : Matrix β α R) :
    (fromBlocks A B C D).submatrix id ⇑(Equiv.sumComm α β) = fromBlocks B A D C := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- **The complementary block relation.**  For a pair of mutually inverse matrices written in
opposite block shapes, the lower left blocks have proportional determinants, the factor being the
determinant of the first matrix with its column blocks exchanged. -/
theorem det_toBlocks₂₁_eq (H : Matrix (α ⊕ β) (β ⊕ α) R) (E : Matrix (β ⊕ α) (α ⊕ β) R)
    (h : H * E = 1) :
    H.toBlocks₂₁.det = (H.submatrix id ⇑(Equiv.sumComm α β)).det * E.toBlocks₂₁.det := by
  set A := H.toBlocks₁₁ with hA
  set B := H.toBlocks₁₂ with hB
  set C := H.toBlocks₂₁ with hC
  set D := H.toBlocks₂₂ with hD
  set A' := E.toBlocks₁₁ with hA'
  set B' := E.toBlocks₁₂ with hB'
  set C' := E.toBlocks₂₁ with hC'
  set D' := E.toBlocks₂₂ with hD'
  have hH : H = fromBlocks A B C D := (fromBlocks_toBlocks H).symm
  have hE : E = fromBlocks A' B' C' D' := (fromBlocks_toBlocks E).symm
  have hprod : fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D')
      = fromBlocks (1 : Matrix α α R) 0 0 (1 : Matrix β β R) := by
    rw [← fromBlocks_multiply, ← hH, ← hE, h, fromBlocks_one]
  have h11 : A * A' + B * C' = 1 := (fromBlocks_inj.1 hprod).1
  have h21 : C * A' + D * C' = 0 := (fromBlocks_inj.1 hprod).2.2.1
  have hHG : H * fromBlocks (1 : Matrix β β R) A' 0 C'
      = fromBlocks A (1 : Matrix α α R) C 0 := by
    rw [hH, fromBlocks_multiply, h11, h21]
    simp
  have hG : (fromBlocks (1 : Matrix β β R) A' 0 C').det = C'.det := by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul]
  have hsplit : (H.submatrix id ⇑(Equiv.sumComm α β)) *
      ((fromBlocks (1 : Matrix β β R) A' 0 C').submatrix
        ⇑(Equiv.sumComm α β) ⇑(Equiv.sumComm α β))
      = (H * fromBlocks (1 : Matrix β β R) A' 0 C').submatrix id ⇑(Equiv.sumComm α β) :=
    submatrix_mul_equiv H _ id (Equiv.sumComm α β) _
  have hdet : ((H * fromBlocks (1 : Matrix β β R) A' 0 C').submatrix
      id ⇑(Equiv.sumComm α β)).det = C.det := by
    rw [hHG, submatrix_sumComm_fromBlocks, det_fromBlocks_zero₂₁, det_one, one_mul]
  rw [← hdet, ← hsplit, Matrix.det_mul, det_submatrix_equiv_self, hG]

/-- **Irreducibility passes between the two complementary blocks** whenever the exchanged matrix has
unit determinant. -/
theorem irreducible_det_toBlocks₂₁_iff (H : Matrix (α ⊕ β) (β ⊕ α) R)
    (E : Matrix (β ⊕ α) (α ⊕ β) R) (h : H * E = 1)
    (hu : IsUnit (H.submatrix id ⇑(Equiv.sumComm α β)).det) :
    Irreducible H.toBlocks₂₁.det ↔ Irreducible E.toBlocks₂₁.det := by
  obtain ⟨u, hu'⟩ := hu
  rw [det_toBlocks₂₁_eq H E h, ← hu']
  exact irreducible_units_mul u

/-- **A reindexed matrix of determinant one has unit determinant.**  Reindexing rows and columns by
two bijections changes the determinant by the sign of the permutation comparing them. -/
theorem isUnit_det_submatrix_of_det_eq_one {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    [DecidableEq γ] (M : Matrix ι ι R) (hM : M.det = 1) (e f : γ ≃ ι) :
    IsUnit (M.submatrix ⇑e ⇑f).det := by
  have hcomp : M.submatrix (⇑e) (⇑f)
      = (M.submatrix (⇑e) (⇑e)).submatrix id ⇑(f.trans e.symm) := by
    ext x y
    simp
  rw [hcomp, det_permute', det_submatrix_equiv_self, hM, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (f.trans e.symm)) with hs | hs <;> rw [hs] <;> simp

end GaloisForLFunctions.HTGeometry
