import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockHarishChandraInduction

/-! The superdiagonal sum splits across diagonal blocks, including zero-size blocks. -/

noncomputable section
open scoped Classical

open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ}

private theorem entN_finIndex {n : ℕ} (M : Mt g n) (i j : Fin n) : entN M i.val j.val = M i j := by
  simp [entN, i.isLt, j.isLt]

private theorem superdiagonal_sum_full {n : ℕ} (M : Mt g n) :
    (∑ i ∈ Finset.range (n - 1), entN M i (i + 1)) =
      ∑ i ∈ Finset.range n, entN M i (i + 1) := by
  refine Finset.sum_subset (Finset.range_mono (Nat.sub_le n 1)) fun i hi hn => ?_
  have h : ¬i + 1 < n := by
    rw [Finset.mem_range] at hi hn
    omega
  simp [entN, h]

private theorem entN_diagonal_left (A : Mt g a) (B : Mt g b) {k : ℕ} (hk : k < a) :
    entN (upperBlockMatrix A 0 B) k (k + 1) = entN A k (k + 1) := by
  by_cases hk' : k + 1 < a
  · let i : Fin a := ⟨k, hk⟩
    let j : Fin a := ⟨k + 1, hk'⟩
    change entN (upperBlockMatrix A 0 B) (Fin.castAdd b i).val (Fin.castAdd b j).val = entN A i.val j.val
    rw [entN_finIndex, entN_finIndex]
    simp [upperBlockMatrix]
  · by_cases hb : 0 < b
    · have ht : entN A k (k + 1) = 0 := by simp [entN, hk']
      rw [ht, show k + 1 = a by omega]
      let i : Fin a := ⟨k, hk⟩
      let j : Fin b := ⟨0, hb⟩
      change entN (upperBlockMatrix A 0 B) (Fin.castAdd b i).val (Fin.natAdd a j).val = 0
      rw [entN_finIndex]
      simp [upperBlockMatrix]
    · have ht : ¬k + 1 < a + b := by omega
      simp [entN, hk', ht]

private theorem entN_diagonal_right (A : Mt g a) (B : Mt g b) {k : ℕ} (hk : k < b) :
    entN (upperBlockMatrix A 0 B) (a + k) (a + k + 1) = entN B k (k + 1) := by
  by_cases hk' : k + 1 < b
  · let i : Fin b := ⟨k, hk⟩
    let j : Fin b := ⟨k + 1, hk'⟩
    have hj : a + k + 1 = (Fin.natAdd a j).val := by
      change a + k + 1 = a + (k + 1)
      omega
    rw [hj]
    change entN (upperBlockMatrix A 0 B) (Fin.natAdd a i).val (Fin.natAdd a j).val = entN B i.val j.val
    rw [entN_finIndex, entN_finIndex]
    simp [upperBlockMatrix]
  · have ht : ¬a + k + 1 < a + b := by omega
    simp [entN, hk', ht]

/-- A block diagonal matrix has superdiagonal sum equal to the sum for its two blocks. -/
theorem superdiagonal_blockDiagonal (A : Mt g a) (B : Mt g b) :
    (∑ i ∈ Finset.range (a + b - 1), entN (upperBlockMatrix A 0 B) i (i + 1)) =
      (∑ i ∈ Finset.range (a - 1), entN A i (i + 1)) +
        ∑ i ∈ Finset.range (b - 1), entN B i (i + 1) := by
  rw [superdiagonal_sum_full (upperBlockMatrix A 0 B), superdiagonal_sum_full A, superdiagonal_sum_full B,
    Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => entN_diagonal_left A B (Finset.mem_range.mp hi)) ?_
  exact Finset.sum_congr rfl fun i hi => entN_diagonal_right A B (Finset.mem_range.mp hi)

/-- Reindexing a square matrix by equality of dimensions preserves the superdiagonal sum. -/
theorem superdiagonal_submatrix_finCongr {n m : ℕ} (h : n = m) (A : Mt g m) :
    (∑ i ∈ Finset.range (n - 1), entN (A.submatrix (finCongr h) (finCongr h)) i (i + 1)) =
      ∑ i ∈ Finset.range (m - 1), entN A i (i + 1) := by
  subst m
  rfl

end GlobalTheory.GLq
