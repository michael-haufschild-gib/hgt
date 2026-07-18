import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Terminal-linear Jacobian reduction

If an output coordinate is terminal-linear, its jet Jacobian has a bordered form.  Subtracting
the Bell multiplier of the terminal row from every higher row removes the terminal column; the
remaining block is a common scalar multiple of the lower-state Jacobian.  The determinant formula
below isolates this purely algebraic step, including its sign.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The bordered matrix produced by a terminal-linear output.  The first row differentiates the
terminal coordinate itself.  Each later row has terminal derivative `B i` and lower-coordinate
gradient `x • L i`. -/
def terminalLinearJacobianMatrix {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i => Fin.cases
    (Fin.lastCases 1 (fun _ => 0))
    (fun r => Fin.lastCases (B r) (fun c => x * L r c)) i

@[simp]
theorem terminalLinearJacobianMatrix_zero_castSucc {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    terminalLinearJacobianMatrix x B L 0 j.castSucc = 0 := by
  simp [terminalLinearJacobianMatrix]

@[simp]
theorem terminalLinearJacobianMatrix_zero_last {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    terminalLinearJacobianMatrix x B L 0 (Fin.last n) = 1 := by
  simp [terminalLinearJacobianMatrix]

@[simp]
theorem terminalLinearJacobianMatrix_succ_castSucc {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    terminalLinearJacobianMatrix x B L i.succ j.castSucc = x * L i j := by
  simp [terminalLinearJacobianMatrix]

@[simp]
theorem terminalLinearJacobianMatrix_succ_last {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    terminalLinearJacobianMatrix x B L i.succ (Fin.last n) = B i := by
  simp [terminalLinearJacobianMatrix]

/-- **Terminal-linear determinant reduction.**  The terminal multipliers `B` disappear from the
determinant, while every lower row contributes one factor of `x`. -/
theorem terminalLinearJacobianMatrix_det {R : Type*} [CommRing R] {n : ℕ}
    (x : R) (B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    (terminalLinearJacobianMatrix x B L).det =
      (-1 : R) ^ n * x ^ n * L.det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have hminor :
        (terminalLinearJacobianMatrix x B L).submatrix Fin.succ (Fin.last n).succAbove =
          x • L := by
      ext i j
      simp [smul_eq_mul]
    rw [hminor, Matrix.det_smul]
    simp [mul_assoc]
  · intro j _ hj
    have hjlt : j < Fin.last n := (Fin.lt_last_iff_ne_last).2 hj
    have ⟨k, hk⟩ : ∃ k : Fin n, j = k.castSucc := by
      exact ⟨j.castPred (Fin.ne_of_lt hjlt), by simp⟩
    subst j
    simp
  · simp

end GaloisForLFunctions

end
