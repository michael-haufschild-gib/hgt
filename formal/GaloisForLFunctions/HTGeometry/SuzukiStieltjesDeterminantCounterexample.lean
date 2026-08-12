import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin

/-!
# Determinant-chain obstruction in Suzuki's Stieltjes argument

The converse proof of Suzuki's 2022 Theorem 1.8 passes from nonnegative leading determinants of
a Hankel sequence and its shift to Stieltjes positivity.  That generic implication fails when a
leading determinant vanishes.  This module gives a single exact sequence for which both complete
determinant chains are nonnegative but the shifted moment form is negative.

The determinant proof is analytic: repeated rows handle the small singular blocks, zero columns
handle every later block, and the two exceptional nonsingular blocks are triangularized by column
reversal.  No numerical determinant certificate is used.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- The finite initial-one sequence: `1, ..., 1, 0, 0, ...`. -/
def initialOneSequence (N k : ℕ) : ℝ :=
  if k ≤ N then 1 else 0

@[simp] theorem initialOneSequence_of_le {N k : ℕ} (h : k ≤ N) :
    initialOneSequence N k = 1 := by simp [initialOneSequence, h]

@[simp] theorem initialOneSequence_of_lt {N k : ℕ} (h : N < k) :
    initialOneSequence N k = 0 := by simp [initialOneSequence, Nat.not_le.mpr h]

theorem initialOneSequence_succ (N k : ℕ) :
    initialOneSequence (N + 1) (k + 1) = initialOneSequence N k := by
  simp only [initialOneSequence, Nat.add_le_add_iff_right]

theorem revPerm_sign_fin_four : Equiv.Perm.sign (@Fin.revPerm 4) = 1 := by
  have hperm : (@Fin.revPerm 4) =
      Equiv.swap (0 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 := by
    ext i
    fin_cases i <;> rfl
  rw [hperm, Equiv.Perm.sign_mul]
  rw [Equiv.Perm.sign_swap (by omega : (0 : Fin 4) ≠ 3)]
  rw [Equiv.Perm.sign_swap (by omega : (1 : Fin 4) ≠ 2)]
  norm_num

theorem revPerm_sign_fin_five : Equiv.Perm.sign (@Fin.revPerm 5) = 1 := by
  have hperm : (@Fin.revPerm 5) =
      Equiv.swap (0 : Fin 5) 4 * Equiv.swap (1 : Fin 5) 3 := by
    ext i
    fin_cases i <;> rfl
  rw [hperm, Equiv.Perm.sign_mul]
  rw [Equiv.Perm.sign_swap (by omega : (0 : Fin 5) ≠ 4)]
  rw [Equiv.Perm.sign_swap (by omega : (1 : Fin 5) ≠ 3)]
  norm_num

theorem det_momentHankelMatrix_initialOneSequence_top
    (N : ℕ) (hsign : Equiv.Perm.sign (@Fin.revPerm (N + 1)) = 1) :
    (momentHankelMatrix (initialOneSequence N) (N + 1)).det = 1 := by
  let M := momentHankelMatrix (initialOneSequence N) (N + 1)
  let U := M.submatrix id (@Fin.revPerm (N + 1))
  have hentry (i j : Fin (N + 1)) :
      U i j = if i ≤ j then 1 else 0 := by
    have hiff : (i : ℕ) + (j.rev : ℕ) ≤ N ↔ i ≤ j := by
      have hj : (j : ℕ) + (j.rev : ℕ) = N := Fin.add_rev_cast j
      change (i : ℕ) + (j.rev : ℕ) ≤ N ↔ (i : ℕ) ≤ (j : ℕ)
      omega
    simp only [U, M, Matrix.submatrix_apply, id_eq, Fin.revPerm_apply,
      momentHankelMatrix, initialOneSequence, hiff]
  have htri : U.BlockTriangular id := by
    intro i j hji
    rw [hentry]
    change j < i at hji
    simp [not_le_of_gt hji]
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    simp [hentry]
  have hperm := Matrix.det_permute' (@Fin.revPerm (N + 1)) M
  have hdetUM : U.det = M.det := by
    simpa [U, hsign] using hperm
  exact hdetUM.symm.trans hdetU

/-- Sequence used to refute the determinant-only Stieltjes inference in Suzuki's proof. -/
def suzukiDeterminantCounterexample : ℕ → ℝ := initialOneSequence 4

theorem det_momentHankelMatrix_suzukiCounterexample_top :
    (momentHankelMatrix suzukiDeterminantCounterexample 5).det = 1 := by
  exact det_momentHankelMatrix_initialOneSequence_top 4 revPerm_sign_fin_five

theorem det_momentHankelMatrix_shift_suzukiCounterexample_top :
    (momentHankelMatrix (fun k => suzukiDeterminantCounterexample (k + 1)) 4).det = 1 := by
  have hseq : (fun k => suzukiDeterminantCounterexample (k + 1)) = initialOneSequence 3 := by
    funext k
    exact initialOneSequence_succ 3 k
  rw [hseq]
  exact det_momentHankelMatrix_initialOneSequence_top 3 revPerm_sign_fin_four

theorem det_momentHankelMatrix_suzukiCounterexample_nonneg (n : ℕ) :
    0 ≤ (momentHankelMatrix suzukiDeterminantCounterexample (n + 1)).det := by
  by_cases hn : n ≤ 4
  · interval_cases n
    · simp [momentHankelMatrix, suzukiDeterminantCounterexample, initialOneSequence]
    · rw [Matrix.det_zero_of_row_eq (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by omega)]
      ext j
      fin_cases j <;> simp [momentHankelMatrix, suzukiDeterminantCounterexample,
        initialOneSequence]
    · rw [Matrix.det_zero_of_row_eq (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by omega)]
      ext j
      fin_cases j <;> simp [momentHankelMatrix, suzukiDeterminantCounterexample,
        initialOneSequence]
    · rw [Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by omega)]
      ext j
      fin_cases j <;> simp [momentHankelMatrix, suzukiDeterminantCounterexample,
        initialOneSequence]
    · rw [det_momentHankelMatrix_suzukiCounterexample_top]
      norm_num
  · have hn5 : 5 ≤ n := by omega
    let j : Fin (n + 1) := ⟨5, by omega⟩
    rw [Matrix.det_eq_zero_of_column_eq_zero j]
    intro i
    change initialOneSequence 4 ((i : ℕ) + 5) = 0
    apply initialOneSequence_of_lt
    omega

theorem det_momentHankelMatrix_shift_suzukiCounterexample_nonneg (n : ℕ) :
    0 ≤ (momentHankelMatrix
      (fun k => suzukiDeterminantCounterexample (k + 1)) (n + 1)).det := by
  have hseq : (fun k => suzukiDeterminantCounterexample (k + 1)) = initialOneSequence 3 := by
    funext k
    exact initialOneSequence_succ 3 k
  rw [hseq]
  by_cases hn : n ≤ 3
  · interval_cases n
    · simp [momentHankelMatrix, initialOneSequence]
    · rw [Matrix.det_zero_of_row_eq (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by omega)]
      ext j
      fin_cases j <;> simp [momentHankelMatrix, initialOneSequence]
    · rw [Matrix.det_zero_of_row_eq (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by omega)]
      ext j
      fin_cases j <;> simp [momentHankelMatrix, initialOneSequence]
    · rw [det_momentHankelMatrix_initialOneSequence_top 3 revPerm_sign_fin_four]
      norm_num
  · have hn4 : 4 ≤ n := by omega
    let j : Fin (n + 1) := ⟨4, by omega⟩
    rw [Matrix.det_eq_zero_of_column_eq_zero j]
    intro i
    change initialOneSequence 3 ((i : ℕ) + 4) = 0
    apply initialOneSequence_of_lt
    omega

theorem suzukiCounterexample_shiftedMomentFunctional_neg :
    momentFunctional suzukiDeterminantCounterexample
      (X * (X ^ 2 - X) ^ 2) = -1 := by
  rw [show X * (X ^ 2 - X) ^ 2 = X ^ 5 - 2 • X ^ 4 + X ^ 3 by ring]
  rw [momentFunctional_add, momentFunctional_sub]
  rw [two_smul, momentFunctional_add]
  simp [momentFunctional_X_pow, suzukiDeterminantCounterexample, initialOneSequence]

/-- Nonnegative leading Hankel determinants for a sequence and its shift do not imply
Stieltjes positivity. This is the precise generic inference used in the converse of Suzuki's
Theorem 1.8. -/
theorem exists_nonnegative_hankel_determinant_chains_not_stieltjesPositive :
    ∃ s : ℕ → ℝ,
      (∀ n, 0 ≤ (momentHankelMatrix s (n + 1)).det) ∧
      (∀ n, 0 ≤ (momentHankelMatrix (fun k => s (k + 1)) (n + 1)).det) ∧
      ¬ (∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2)) := by
  refine ⟨suzukiDeterminantCounterexample,
    det_momentHankelMatrix_suzukiCounterexample_nonneg,
    det_momentHankelMatrix_shift_suzukiCounterexample_nonneg, ?_⟩
  intro h
  have := h (X ^ 2 - X)
  rw [suzukiCounterexample_shiftedMomentFunctional_neg] at this
  norm_num at this

end HTGeometry
