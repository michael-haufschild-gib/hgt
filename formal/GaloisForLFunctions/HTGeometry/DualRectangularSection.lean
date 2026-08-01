import GaloisForLFunctions.HTGeometry.BlockComplementaryMinor
import GaloisForLFunctions.HTGeometry.DualTriangularInverse
import GaloisForLFunctions.HTGeometry.SchurSectionIrreducible

/-!
# Exchanging the two parameters of a rectangular section

A rectangular section of the triangular matrix of complete homogeneous coefficients sits inside that
matrix as one of two complementary blocks: cutting the ambient index at the shift on one side and at
the height on the other exhibits the section as the lower left block.  The same cut applied to the
inverse matrix exhibits the section with the two parameters exchanged, in the dual family, as the
lower left block of the inverse.

The complementary block relation therefore says that the two sections have proportional
determinants, with a unit factor, and the exchange of the two coefficient families turns the dual
section back into an ordinary one.  So a rectangular section is irreducible for one order of the
parameters exactly when it is for the other, and the restriction to shift at least the height
disappears.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-! ## The two cuts of the ambient index -/

/-- Cutting the ambient index at the shift. -/
def schurRowSplit (n m : ℕ) : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv

/-- Cutting the ambient index at the height. -/
def schurColSplit (n m : ℕ) : Fin m ⊕ Fin n ≃ Fin (n + m) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm m n))

theorem schurRowSplit_inl_val {n m : ℕ} (j : Fin n) :
    ((schurRowSplit n m (Sum.inl j) : Fin (n + m)) : ℕ) = (j : ℕ) := by
  simp [schurRowSplit]

theorem schurRowSplit_inr_val {n m : ℕ} (r : Fin m) :
    ((schurRowSplit n m (Sum.inr r) : Fin (n + m)) : ℕ) = n + (r : ℕ) := by
  simp [schurRowSplit]

theorem schurColSplit_inl_val {n m : ℕ} (i : Fin m) :
    ((schurColSplit n m (Sum.inl i) : Fin (n + m)) : ℕ) = (i : ℕ) := by
  simp [schurColSplit]

theorem schurColSplit_inr_val {n m : ℕ} (q : Fin n) :
    ((schurColSplit n m (Sum.inr q) : Fin (n + m)) : ℕ) = m + (q : ℕ) := by
  simp [schurColSplit, Nat.add_comm]

/-! ## The two matrices in block shape -/

/-- The triangular matrix of coefficients, cut at the shift in the rows and at the height in the
columns. -/
noncomputable def schurBlock (K : Type*) [Field K] (L n m : ℕ) :
    Matrix (Fin n ⊕ Fin m) (Fin m ⊕ Fin n) (MvPolynomial (Fin L) K) :=
  (schurTri K L (n + m)).submatrix ⇑(schurRowSplit n m) ⇑(schurColSplit n m)

/-- The inverse matrix, cut the opposite way. -/
noncomputable def dualBlock (K : Type*) [Field K] (L n m : ℕ) :
    Matrix (Fin m ⊕ Fin n) (Fin n ⊕ Fin m) (MvPolynomial (Fin L) K) :=
  (dualTri K L (n + m)).submatrix ⇑(schurColSplit n m) ⇑(schurRowSplit n m)

/-- **The two block matrices are inverse.** -/
theorem schurBlock_mul_dualBlock {L n m : ℕ} :
    schurBlock K L n m * dualBlock K L n m = 1 := by
  rw [schurBlock, dualBlock, Matrix.submatrix_mul_equiv, schurTri_mul_dualTri,
    Matrix.submatrix_one_equiv]

/-- **The lower left block is the rectangular section.** -/
theorem toBlocks₂₁_schurBlock {L n m : ℕ} :
    (schurBlock K L n m).toBlocks₂₁ = rectangularSchurToeplitz (schurVar K L) n m := by
  refine Matrix.ext fun r i => ?_
  show schurTri K L (n + m) (schurRowSplit n m (Sum.inr r)) (schurColSplit n m (Sum.inl i)) = _
  rw [schurTri_apply, schurColSplit_inl_val, schurRowSplit_inr_val]
  rfl

/-- **The lower left block of the inverse is the rectangular section of the dual family with the two
parameters exchanged**, up to a sign in each row and each column. -/
theorem dualBlock_toBlocks₂₁_apply {L n m : ℕ} (q j : Fin n) :
    (dualBlock K L n m).toBlocks₂₁ q j =
      (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ)) *
        ((-1 : MvPolynomial (Fin L) K) ^ (j : ℕ) *
          rectangularSchurToeplitz (dualVar K L) m n q j) := by
  show dualTri K L (n + m) (schurColSplit n m (Sum.inr q)) (schurRowSplit n m (Sum.inl j)) = _
  rw [dualTri_apply, schurColSplit_inr_val, schurRowSplit_inl_val]
  simp only [rectangularSchurToeplitz]
  by_cases hj : (j : ℕ) ≤ m + (q : ℕ)
  · rw [if_pos hj, if_pos hj]
    have hsign : (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ)) *
        (-1 : MvPolynomial (Fin L) K) ^ (j : ℕ) =
        (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ) - (j : ℕ)) := by
      rw [← pow_add, show m + (q : ℕ) + (j : ℕ) = (m + (q : ℕ) - (j : ℕ)) + 2 * (j : ℕ) from by omega,
        pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [← mul_assoc, hsign]
  · rw [if_neg hj, if_neg hj, mul_zero, mul_zero]

/-- **The determinant of the dual block is a unit multiple of the exchanged section.** -/
theorem det_toBlocks₂₁_dualBlock {L n m : ℕ} :
    (dualBlock K L n m).toBlocks₂₁.det =
      (∏ q : Fin n, (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ))) *
        ((∏ j : Fin n, (-1 : MvPolynomial (Fin L) K) ^ (j : ℕ)) *
          (rectangularSchurToeplitz (dualVar K L) m n).det) := by
  have h1 : (dualBlock K L n m).toBlocks₂₁
      = Matrix.of (fun (q j : Fin n) => (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ)) *
          (Matrix.of (fun (q j : Fin n) => (-1 : MvPolynomial (Fin L) K) ^ (j : ℕ) *
            rectangularSchurToeplitz (dualVar K L) m n q j) q j)) :=
    Matrix.ext fun q j => dualBlock_toBlocks₂₁_apply q j
  rw [h1, Matrix.det_mul_column, Matrix.det_mul_row]

/-- **Irreducibility is insensitive to the signs.** -/
theorem irreducible_det_toBlocks₂₁_dualBlock_iff {L n m : ℕ} :
    Irreducible ((dualBlock K L n m).toBlocks₂₁.det) ↔
      Irreducible ((rectangularSchurToeplitz (dualVar K L) m n).det) := by
  rw [det_toBlocks₂₁_dualBlock, ← mul_assoc]
  have hu : IsUnit ((∏ q : Fin n, (-1 : MvPolynomial (Fin L) K) ^ (m + (q : ℕ))) *
      ∏ j : Fin n, (-1 : MvPolynomial (Fin L) K) ^ (j : ℕ)) := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add]
    exact (isUnit_one.neg).pow _
  obtain ⟨u, hu'⟩ := hu
  rw [← hu']
  exact irreducible_units_mul u

/-- **The exchanged matrix has unit determinant**, being a reindexing of a matrix of determinant
one. -/
theorem isUnit_det_schurBlock_swap {L n m : ℕ} :
    IsUnit ((schurBlock K L n m).submatrix id ⇑(Equiv.sumComm (Fin n) (Fin m))).det := by
  have h : (schurBlock K L n m).submatrix id ⇑(Equiv.sumComm (Fin n) (Fin m))
      = (schurTri K L (n + m)).submatrix ⇑(schurRowSplit n m)
          ⇑((Equiv.sumComm (Fin n) (Fin m)).trans (schurColSplit n m)) := rfl
  rw [h]
  exact isUnit_det_submatrix_of_det_eq_one _ det_schurTri _ _

/-! ## The exchange of parameters -/

/-- **A rectangular section is irreducible for one order of the parameters exactly when the dual
section is for the other.** -/
theorem irreducible_det_rect_swap_iff {L n m : ℕ} :
    Irreducible ((rectangularSchurToeplitz (schurVar K L) n m).det) ↔
      Irreducible ((rectangularSchurToeplitz (dualVar K L) m n).det) := by
  rw [← toBlocks₂₁_schurBlock (K := K) (L := L) (n := n) (m := m),
    ← irreducible_det_toBlocks₂₁_dualBlock_iff]
  exact irreducible_det_toBlocks₂₁_iff _ _ schurBlock_mul_dualBlock isUnit_det_schurBlock_swap

/-- **The exchange of the two coefficient families carries a section to the section of the dual
family.** -/
theorem dualSub_det_rect {L m n : ℕ} (hL : m + n - 1 ≤ L) :
    dualSub K L ((rectangularSchurToeplitz (schurVar K L) m n).det)
      = (rectangularSchurToeplitz (dualVar K L) m n).det := by
  have hmap : (dualSub K L).mapMatrix (rectangularSchurToeplitz (schurVar K L) m n)
      = rectangularSchurToeplitz (dualVar K L) m n := by
    refine Matrix.ext fun r i => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
    simp only [rectangularSchurToeplitz]
    by_cases h : (i : ℕ) ≤ m + (r : ℕ)
    · rw [if_pos h, if_pos h]
      have hr := r.isLt
      exact dualSub_schurVar (by omega)
    · rw [if_neg h, if_neg h, map_zero]
  rw [AlgHom.map_det, hmap]

/-- **Every rectangular section is irreducible.**  For shift at least the height this is the
induction on the corner expansion; for shift below the height the complementary block relation and
the exchange of the two coefficient families reduce it to that case with the parameters
exchanged. -/
theorem irreducible_det_rectangularSchurToeplitz [DecidableEq K] {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    Irreducible ((rectangularSchurToeplitz (schurVar K (n + m - 1)) n m).det) := by
  rcases le_or_gt m n with h | h
  · exact irreducible_det_schur_of_le hm h
  · have hbase : Irreducible ((rectangularSchurToeplitz (schurVar K (m + n - 1)) m n).det) :=
      irreducible_det_schur_of_le hn (le_of_lt h)
    rw [show m + n - 1 = n + m - 1 from by omega] at hbase
    refine irreducible_det_rect_swap_iff.2 ?_
    rw [← dualSub_det_rect (by omega : m + n - 1 ≤ n + m - 1)]
    exact (irreducible_dualSub_iff _).2 hbase

end GaloisForLFunctions.HTGeometry
