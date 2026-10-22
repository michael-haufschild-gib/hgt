import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLowTailCoordinates
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Consecutive universal Hankel determinants do not divide each other

Let `c₀ = 1` and `c_{k+1} = X_k` in the polynomial ring `ℤ[X₀, X₁, ...]`, and let `D_n` be the
leading `n × n` Hankel determinant `det (c_{i+j})_{i,j<n}`. This module evaluates at the point
`X_n = 1`, `X_k = 0` for `k ≠ n`, so that `c_s ↦ 1` exactly when `s = 0` or `s = n + 1`. Under
this evaluation `D_n ↦ 0` for `n ≥ 2` (its second row vanishes), while `D_{n+1} ↦ ±1` (the matrix
becomes a block of `1` and a reversal permutation). Hence `D_n` does not divide `D_{n+1}`.

## Main results

- `deningerHazewinkelBoundaryMinorEval`: the evaluation ring homomorphism `ℤ[X] → ℤ` above.
- `deningerHazewinkelBoundaryMinorEval_leading_eq_zero`: for `n ≥ 2`, `D_n` evaluates to `0`.
- `deningerHazewinkelBoundaryMinorEval_leading_succ_isUnit`: `D_{n+1}` evaluates to a unit of `ℤ`.
- `deningerHazewinkelLeading_not_dvd_leading_succ`: for `n ≥ 2`, `D_n ∤ D_{n+1}`.

## Hypotheses

Unconditional; the only premise is `2 ≤ n`.
-/

namespace RHTower
noncomputable section

/-- Evaluation `ℤ[X₀, X₁, ...] → ℤ` sending `X_n` to `1` and every other variable to `0`. -/
def deningerHazewinkelBoundaryMinorEval (n : ℕ) :
    MvPolynomial ℕ ℤ →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) fun k => if k = n then 1 else 0

/-- Under the evaluation, the universal Hankel coefficient `c_s` becomes `1` if `s = 0` or `s = n + 1`,
and `0` otherwise. -/
theorem deningerHazewinkelBoundaryMinorEval_coeff (n s : ℕ) :
    deningerHazewinkelBoundaryMinorEval n
      (deningerHazewinkelUniversalCoeff s) =
      if s = 0 ∨ s = n + 1 then 1 else 0 := by
  cases s with
  | zero => simp [deningerHazewinkelBoundaryMinorEval,
      deningerHazewinkelUniversalCoeff]
  | succ s =>
      simp [deningerHazewinkelBoundaryMinorEval,
        deningerHazewinkelUniversalCoeff]

/-- For `n ≥ 2`, the leading Hankel determinant `D_n` evaluates to `0`. -/
theorem deningerHazewinkelBoundaryMinorEval_leading_eq_zero
    (n : ℕ) (hn : 2 ≤ n) :
    deningerHazewinkelBoundaryMinorEval n
      (deningerHazewinkelLeadingDeterminant n) = 0 := by
  rw [deningerHazewinkelLeadingDeterminant]
  rw [(deningerHazewinkelBoundaryMinorEval n).map_det]
  change Matrix.det (fun i j : Fin n =>
    deningerHazewinkelBoundaryMinorEval n
      (deningerHazewinkelUniversalCoeff (i.val + j.val))) = 0
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨1, by omega⟩
  intro j
  rw [deningerHazewinkelBoundaryMinorEval_coeff]
  change (if 1 + j.val = 0 ∨ 1 + j.val = n + 1 then 1 else 0) = 0
  rw [if_neg]
  omega

/-- The next leading Hankel determinant `D_{n+1}` evaluates to a unit `±1` of `ℤ`. -/
theorem deningerHazewinkelBoundaryMinorEval_leading_succ_isUnit
    (n : ℕ) :
    IsUnit (deningerHazewinkelBoundaryMinorEval n
      (deningerHazewinkelLeadingDeterminant (n + 1))) := by
  rw [deningerHazewinkelLeadingDeterminant]
  rw [(deningerHazewinkelBoundaryMinorEval n).map_det]
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
    finSumFinEquiv |>.trans (finCongr (Nat.add_comm 1 n))
  let P : Matrix (Fin n) (Fin n) ℤ := (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℤ
  let B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ :=
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ)
      0 0 P
  have hmatrix : (fun i j : Fin (n + 1) =>
      deningerHazewinkelBoundaryMinorEval n
        (deningerHazewinkelUniversalCoeff (i.val + j.val))) =
      B.submatrix e.symm e.symm := by
    apply Matrix.ext
    intro i j
    rw [deningerHazewinkelBoundaryMinorEval_coeff]
    rcases hri : e.symm i with i' | i' <;>
      rcases hrj : e.symm j with j' | j'
    · have hi : i = e (Sum.inl i') := by rw [← hri]; simp
      have hj : j = e (Sum.inl j') := by rw [← hrj]; simp
      subst i
      subst j
      fin_cases i'
      fin_cases j'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      simp [B, e, finSumFinEquiv_apply_left]
    · have hi : i = e (Sum.inl i') := by rw [← hri]; simp
      have hj : j = e (Sum.inr j') := by rw [← hrj]; simp
      subst i
      subst j
      fin_cases i'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      simp [B, e, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Nat.ne_of_lt j'.isLt]
    · have hi : i = e (Sum.inr i') := by rw [← hri]; simp
      have hj : j = e (Sum.inl j') := by rw [← hrj]; simp
      subst i
      subst j
      fin_cases j'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      simp [B, e, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Nat.ne_of_lt i'.isLt]
    · have hi : i = e (Sum.inr i') := by rw [← hri]; simp
      have hj : j = e (Sum.inr j') := by rw [← hrj]; simp
      subst i
      subst j
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_right]
      change (if 1 + i'.val + (1 + j'.val) = 0 ∨
        1 + i'.val + (1 + j'.val) = n + 1 then 1 else 0) = P i' j'
      have hiff : 1 + i'.val + (1 + j'.val) = n + 1 ↔ i'.rev = j' := by
        constructor
        · intro h
          apply Fin.ext
          have hrev : i'.rev.val = n - (i'.val + 1) := rfl
          omega
        · intro h
          rw [← h]
          have hrev : i'.rev.val = n - (i'.val + 1) := rfl
          omega
      simp [hiff, P, Equiv.Perm.permMatrix]
  change IsUnit (Matrix.det (fun i j : Fin (n + 1) =>
    deningerHazewinkelBoundaryMinorEval n
      (deningerHazewinkelUniversalCoeff (i.val + j.val))))
  rw [hmatrix, Matrix.det_submatrix_equiv_self]
  dsimp only [B]
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  dsimp only [P]
  rw [Matrix.det_permutation]
  exact (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))).isUnit

/-- For `n ≥ 2`, the universal Hankel determinant `D_n` does not divide `D_{n+1}` in
`ℤ[X₀, X₁, ...]`. -/
theorem deningerHazewinkelLeading_not_dvd_leading_succ
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ deningerHazewinkelLeadingDeterminant n ∣
      deningerHazewinkelLeadingDeterminant (n + 1) := by
  intro hdvd
  have hmap := map_dvd (deningerHazewinkelBoundaryMinorEval n) hdvd
  rw [deningerHazewinkelBoundaryMinorEval_leading_eq_zero n hn] at hmap
  exact (deningerHazewinkelBoundaryMinorEval_leading_succ_isUnit n).ne_zero
    (zero_dvd_iff.mp hmap)

end
end RHTower

