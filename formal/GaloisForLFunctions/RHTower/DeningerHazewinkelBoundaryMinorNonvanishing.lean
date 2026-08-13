import GaloisForLFunctions.RHTower.DeningerHazewinkelLowTailCoordinates
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace RHTower
noncomputable section

def deningerHazewinkelBoundaryMinorEval (n : ℕ) :
    MvPolynomial ℕ ℤ →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) fun k => if k = n then 1 else 0

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

