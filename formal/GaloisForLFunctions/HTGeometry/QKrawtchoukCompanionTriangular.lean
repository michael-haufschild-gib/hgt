import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionBirthDeath
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact triangularization of the finite companion birth-death matrix

Evaluation on the geometric lattice is an invertible Vandermonde matrix.
The monomial action therefore gives the characteristic polynomial of the
concrete birth-death representation as a product of explicit linear factors.
These are the two finite spectral branches behind arXiv:2609.24149, Remark 8.5.
-/

noncomputable section

namespace HTGeometry

private def up (K : ℕ) (i : Fin (2 * K + 1)) : Fin (2 * K + 1) :=
  ⟨min (i.val + 1) (2 * K), by omega⟩

private def down (K : ℕ) (i : Fin (2 * K + 1)) : Fin (2 * K + 1) :=
  ⟨i.val - 1, by omega⟩

private def lowerMode (t u j : ℝ) : ℝ :=
  Real.exp u * Real.exp (Real.exp t * j) - Real.exp (-Real.exp t * j) + 1 - Real.exp u

/-- The concrete birth-death matrix on the finite companion block. -/
def qKrawtchoukCompanionBirthDeathMatrix (t u : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℝ := fun i j =>
  (if i = j then qKrawtchoukCompanionFiniteDiagonal t u K i else 0) +
  (if up K i = j then qKrawtchoukCompanionBirth t u K i else 0) +
  (if down K i = j then qKrawtchoukCompanionDeath t i else 0)

/-- Evaluation of the monomial basis on the geometric lattice. -/
def qKrawtchoukCompanionModeBasis (t : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℝ :=
  Matrix.vandermonde fun i => Real.exp (Real.exp t * (i : ℝ))

/-- The upper bidiagonal matrix of the same action in monomial coordinates. -/
def qKrawtchoukCompanionModeMatrix (t u : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℝ := fun i j =>
  (if i = j then qKrawtchoukCompanionModeLevel t u K j else 0) +
  (if i = down K j then lowerMode t u j else 0)

private theorem basis_apply (t : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    qKrawtchoukCompanionModeBasis t K i j = qKrawtchoukCompanionMode t j i := by
  change Real.exp (Real.exp t * (i : ℝ)) ^ (j : ℕ) = _
  rw [← Real.exp_nat_mul]
  unfold qKrawtchoukCompanionMode
  congr 1
  ring

private theorem birth_up (t u : ℝ) (K : ℕ) (f : ℕ → ℝ) (i : Fin (2 * K + 1)) :
    qKrawtchoukCompanionBirth t u K i * f (up K i) =
      qKrawtchoukCompanionBirth t u K i * f (i + 1) := by
  by_cases hi : i.val < 2 * K
  · simp only [up, min_eq_left (by omega : i.val + 1 ≤ 2 * K)]
  · have he : i.val = 2 * K := by omega
    simp [qKrawtchoukCompanionBirth, he]

private theorem left_action (t u : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    (qKrawtchoukCompanionBirthDeathMatrix t u K * qKrawtchoukCompanionModeBasis t K) i j =
      qKrawtchoukCompanionBirthDeath t u K (qKrawtchoukCompanionMode t j) i := by
  simp only [Matrix.mul_apply, qKrawtchoukCompanionBirthDeathMatrix, add_mul,
    ite_mul, zero_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, basis_apply]
  rw [birth_up]
  change _ = qKrawtchoukCompanionBirth t u K i * qKrawtchoukCompanionMode t j (i + 1) +
    qKrawtchoukCompanionDeath t i * qKrawtchoukCompanionMode t j (i.val - 1) +
    qKrawtchoukCompanionFiniteDiagonal t u K i * qKrawtchoukCompanionMode t j i
  dsimp [down]
  ring

private theorem right_action (t u : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    (qKrawtchoukCompanionModeBasis t K * qKrawtchoukCompanionModeMatrix t u K) i j =
      qKrawtchoukCompanionModeLevel t u K j * qKrawtchoukCompanionMode t j i +
      lowerMode t u j * qKrawtchoukCompanionMode t ((j : ℝ) - 1) i := by
  simp only [Matrix.mul_apply, qKrawtchoukCompanionModeMatrix, mul_add,
    mul_ite, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, basis_apply]
  cases hj : j.val with
  | zero => simp [lowerMode, mul_comm]
  | succ k =>
      have hp : ((down K j : Fin (2 * K + 1)) : ℝ) = (j : ℝ) - 1 := by
        simp [down, hj]
      rw [hp]
      simp only [hj]
      ring

/-- The concrete geometric evaluation matrix is invertible. -/
theorem qKrawtchoukCompanionModeBasis_det_ne_zero (t : ℝ) (K : ℕ) :
    (qKrawtchoukCompanionModeBasis t K).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  have h : Real.exp t * (i : ℝ) = Real.exp t * (j : ℝ) := Real.exp_injective hij
  have hij' : (i : ℝ) = (j : ℝ) := mul_left_cancel₀ (Real.exp_pos t).ne' h
  apply Fin.ext
  exact_mod_cast hij'

/-- Exact intertwining between the finite tridiagonal and upper bidiagonal matrices. -/
theorem qKrawtchoukCompanionBirthDeathMatrix_intertwine (t u : ℝ) (K : ℕ) :
    qKrawtchoukCompanionBirthDeathMatrix t u K * qKrawtchoukCompanionModeBasis t K =
      qKrawtchoukCompanionModeBasis t K * qKrawtchoukCompanionModeMatrix t u K := by
  ext i j
  rw [left_action, right_action, qKrawtchoukCompanionBirthDeath_mode]
  rfl

private theorem mode_triangular (t u : ℝ) (K : ℕ) :
    (qKrawtchoukCompanionModeMatrix t u K).BlockTriangular id := by
  intro i j hji
  dsimp only [id] at hji
  have hij : i ≠ j := by omega
  have hip : i ≠ down K j := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [down] at hv
    omega
  simp [qKrawtchoukCompanionModeMatrix, hij, hip]

private theorem mode_diagonal (t u : ℝ) (K : ℕ) (i : Fin (2 * K + 1)) :
    qKrawtchoukCompanionModeMatrix t u K i i = qKrawtchoukCompanionModeLevel t u K i := by
  unfold qKrawtchoukCompanionModeMatrix
  rw [if_pos rfl]
  by_cases hi : i = down K i
  · rw [if_pos hi]
    have hv := congrArg Fin.val hi
    have hz : i.val = 0 := by dsimp [down] at hv; omega
    have h0 : ((i : ℕ) : ℝ) = 0 := by exact_mod_cast hz
    simp only [lowerMode, h0, mul_zero, Real.exp_zero]
    ring
  · rw [if_neg hi, add_zero]

/-- The finite birth-death characteristic polynomial splits into explicit real levels. -/
theorem qKrawtchoukCompanionBirthDeathMatrix_charpoly (t u : ℝ) (K : ℕ) :
    (qKrawtchoukCompanionBirthDeathMatrix t u K).charpoly =
      ∏ j : Fin (2 * K + 1),
        (Polynomial.X - Polynomial.C (qKrawtchoukCompanionModeLevel t u K j)) := by
  let V := qKrawtchoukCompanionModeBasis t K
  have hV : IsUnit V.det := isUnit_iff_ne_zero.mpr
    (qKrawtchoukCompanionModeBasis_det_ne_zero t K)
  have hT : qKrawtchoukCompanionBirthDeathMatrix t u K =
      (V * qKrawtchoukCompanionModeMatrix t u K) * V⁻¹ := by
    calc
      _ = qKrawtchoukCompanionBirthDeathMatrix t u K * (V * V⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hV, mul_one]
      _ = (qKrawtchoukCompanionBirthDeathMatrix t u K * V) * V⁻¹ := by rw [mul_assoc]
      _ = _ := by rw [qKrawtchoukCompanionBirthDeathMatrix_intertwine]
  rw [hT, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hV, one_mul,
    Matrix.charpoly_of_upperTriangular _ (mode_triangular t u K)]
  exact Finset.prod_congr rfl fun j _ => by rw [mode_diagonal]

end HTGeometry
