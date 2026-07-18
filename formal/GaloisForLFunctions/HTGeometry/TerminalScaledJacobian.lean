import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Terminal-scaled Jacobian reduction

For an output `H` satisfying a terminal-linear differential law, every positive jet has the form
`H * Bᵢ`.  Its coordinate gradient is therefore

`H * dBᵢ + Bᵢ * dH`.

Subtracting `Bᵢ` times the first row removes the full gradient of `H`, including its lower-state
components.  If the terminal derivative of every `Bᵢ` vanishes, expansion along the terminal
column leaves the lower `B`-Jacobian, one terminal derivative of `H`, and one factor of `H` from
every remaining row.  This is the algebraic determinant identity behind the positive-power Bell
reduction.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The output-by-coordinate Jacobian before the Bell row shear.  The first row is the arbitrary
gradient `(a,t)` of `H`; row `i+1` is the gradient of `H * Bᵢ`. -/
def terminalScaledJacobianMatrix {R : Type*} [CommRing R] {n : ℕ}
    (H t : R) (a B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i => Fin.cases
    (Fin.lastCases t (fun c => a c))
    (fun r => Fin.lastCases (B r * t) (fun c => H * L r c + B r * a c)) i

/-- The row-reduced terminal-scaled Jacobian. -/
def terminalScaledReducedJacobianMatrix {R : Type*} [CommRing R] {n : ℕ}
    (H t : R) (a : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i => Fin.cases
    (Fin.lastCases t (fun c => a c))
    (fun r => Fin.lastCases 0 (fun c => H * L r c)) i

/-- Adding the Bell multiple of the first row to every later row does not change the determinant. -/
theorem terminalScaledJacobianMatrix_det_eq_reduced
    {R : Type*} [CommRing R] {n : ℕ}
    (H t : R) (a B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    (terminalScaledJacobianMatrix H t a B L).det =
      (terminalScaledReducedJacobianMatrix H t a L).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (c := Fin.cases 0 B) (k := 0)
  · simp
  · intro i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [terminalScaledJacobianMatrix, terminalScaledReducedJacobianMatrix]
    · refine Fin.lastCases ?_ (fun c => ?_) j
      · simp [terminalScaledJacobianMatrix, terminalScaledReducedJacobianMatrix]
      · simp [terminalScaledJacobianMatrix, terminalScaledReducedJacobianMatrix]

/-- The reduced determinant is independent of the lower components of `dH`. -/
theorem terminalScaledReducedJacobianMatrix_det
    {R : Type*} [CommRing R] {n : ℕ}
    (H t : R) (a : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    (terminalScaledReducedJacobianMatrix H t a L).det =
      (-1 : R) ^ n * t * H ^ n * L.det := by
  let M := terminalScaledReducedJacobianMatrix H t a L
  rw [Matrix.det_succ_column M (Fin.last n)]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hminor :
        M.submatrix (0 : Fin (n + 1)).succAbove (Fin.last n).succAbove = H • L := by
      ext i j
      simp [M, terminalScaledReducedJacobianMatrix, smul_eq_mul]
    rw [hminor, Matrix.det_smul]
    simp [M, terminalScaledReducedJacobianMatrix, mul_assoc]
  · intro i _hi hi0
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
    simp [M, terminalScaledReducedJacobianMatrix]
  · simp

/-- **Terminal-scaled determinant reduction.**  The Bell multipliers and the complete lower
gradient of `H` cancel; only its terminal derivative remains. -/
theorem terminalScaledJacobianMatrix_det
    {R : Type*} [CommRing R] {n : ℕ}
    (H t : R) (a B : Fin n → R) (L : Matrix (Fin n) (Fin n) R) :
    (terminalScaledJacobianMatrix H t a B L).det =
      (-1 : R) ^ n * t * H ^ n * L.det := by
  rw [terminalScaledJacobianMatrix_det_eq_reduced,
    terminalScaledReducedJacobianMatrix_det]

/-- Over a domain, nonvanishing of the terminal derivative, output, and lower Jacobian gives a
nonzero full terminal-scaled determinant. -/
theorem terminalScaledJacobianMatrix_det_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (H t : R) (a B : Fin n → R) (L : Matrix (Fin n) (Fin n) R)
    (ht : t ≠ 0) (hH : H ≠ 0) (hL : L.det ≠ 0) :
    (terminalScaledJacobianMatrix H t a B L).det ≠ 0 := by
  rw [terminalScaledJacobianMatrix_det]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ht) (pow_ne_zero _ hH)) hL

end GaloisForLFunctions

end
