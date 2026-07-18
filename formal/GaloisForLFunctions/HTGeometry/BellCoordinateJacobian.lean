import GaloisForLFunctions.HTGeometry.GammaBellSubstitution
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The unit Jacobian of the Bell coordinate change

The finite Bell map

`(x₀, …, xₙ) ↦ (B₁(x), …, Bₙ₊₁(x))`

is triangular with diagonal one.  This file records the corresponding formal derivative matrix
and proves that its determinant is exactly one.  It is the algebraic row-reduction core used when
terminal-linear output jets are replaced by logarithmic-derivative jets.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- A coordinate strictly beyond the frame of a renamed Bell polynomial has zero partial
derivative. -/
theorem pderiv_bellAt_eq_zero_of_lt {n : ℕ} {i j : Fin (n + 1)} (hji : j < i) :
    pderiv i (bellAt n ((j : ℕ) + 1) j.isLt) = 0 := by
  rw [bellAt]
  apply pderiv_eq_zero_of_notMem_vars
  intro hi
  have himage := vars_rename (Fin.castLE j.isLt) (bellCore ((j : ℕ) + 1)) hi
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp himage
  have hval := congrArg Fin.val hk
  simp only [Fin.val_castLE] at hval
  have hklt : (k : ℕ) < (j : ℕ) + 1 := k.isLt
  have hij : (i : ℕ) ≤ (j : ℕ) := by omega
  exact (Nat.not_le_of_lt hji) hij

/-- The partial derivative of the `i`-th Bell coordinate with respect to its newest variable is
one. -/
theorem pderiv_bellAt_diagonal (n : ℕ) (i : Fin (n + 1)) :
    pderiv i (bellAt n ((i : ℕ) + 1) i.isLt) = 1 := by
  rw [bellAt]
  have hlast : Fin.castLE i.isLt (Fin.last (i : ℕ)) = i := by
    apply Fin.ext
    simp
  have hrename := MvPolynomial.pderiv_rename (Fin.castLE_injective i.isLt)
    (Fin.last (i : ℕ)) (bellCore ((i : ℕ) + 1))
  rw [pderiv_last_bellCore, map_one] at hrename
  simpa only [hlast] using hrename

/-- The formal Jacobian of the Bell coordinate family.  Rows are differentiation coordinates and
columns are Bell coordinates. -/
def bellCoordinateJacobian (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) ℂ) :=
  fun i j => pderiv i (bellAt n ((j : ℕ) + 1) j.isLt)

/-- The Bell-coordinate Jacobian is upper triangular. -/
theorem bellCoordinateJacobian_blockTriangular (n : ℕ) :
    Matrix.BlockTriangular (bellCoordinateJacobian n) id := by
  intro i j hji
  exact pderiv_bellAt_eq_zero_of_lt hji

/-- Every diagonal entry of the Bell-coordinate Jacobian is one. -/
theorem bellCoordinateJacobian_diagonal (n : ℕ) (i : Fin (n + 1)) :
    bellCoordinateJacobian n i i = 1 := by
  exact pderiv_bellAt_diagonal n i

/-- **Unit Bell Jacobian.**  The finite Bell coordinate change has determinant exactly one. -/
theorem bellCoordinateJacobian_det (n : ℕ) :
    (bellCoordinateJacobian n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (bellCoordinateJacobian_blockTriangular n)]
  simp [bellCoordinateJacobian_diagonal]

/-- In particular, the Bell coordinate change has a nonzero Jacobian in every finite frame. -/
theorem bellCoordinateJacobian_det_ne_zero (n : ℕ) :
    (bellCoordinateJacobian n).det ≠ 0 := by
  rw [bellCoordinateJacobian_det]
  exact one_ne_zero

end GaloisForLFunctions

end
