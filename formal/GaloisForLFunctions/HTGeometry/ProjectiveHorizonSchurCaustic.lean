import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPureTailFiber

/-!
# The rectangular Schur caustic of the critical horizon map

For an inverse jet `Y`, first-order inversion is `dY = -Y^(2 : ℕ) dX`.  If the raw tail is held fixed,
the critical low-to-high differential is therefore a finite Toeplitz section of the coefficient
sequence of `Y^(2 : ℕ)`.  Its determinant is the rectangular Jacobi--Trudi determinant of shape `n^m`.

This module formalizes the exact truncated tangent identity, the coefficient matrix, and the
determinant identification.  It does not assert the still-open geometric monodromy statement.
-/

open Polynomial
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- First-order reciprocal response to a polynomial perturbation. -/
noncomputable def criticalReciprocalInfinitesimal {K : Type*} [CommRing K]
    (Y dX : K[X]) : K[X] :=
  -(Y * Y * dX)

/-- The reciprocal infinitesimal satisfies the linearized inverse constraint modulo every
truncation at which `X Y = 1`. -/
theorem criticalReciprocalInfinitesimal_tangent {K : Type*} [CommRing K]
    {Xj Y dX : K[X]} {L : ℕ} (hInv : X ^ L ∣ Xj * Y - 1) :
    X ^ L ∣ Xj * criticalReciprocalInfinitesimal Y dX + dX * Y := by
  obtain ⟨q, hq⟩ := hInv
  refine ⟨-(Y * dX) * q, ?_⟩
  calc
    Xj * criticalReciprocalInfinitesimal Y dX + dX * Y =
        -(Y * dX) * (Xj * Y - 1) := by
          simp only [criticalReciprocalInfinitesimal]
          ring
    _ = -(Y * dX) * (X ^ L * q) := by rw [hq]
    _ = X ^ L * (-(Y * dX) * q) := by ring

/-- Rectangular Jacobi--Trudi/Toeplitz section with the convention `h_k=0` for `k<0`. -/
def rectangularSchurToeplitz {K : Type*} [Zero K]
    (h : ℕ → K) (n m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun r i => if (i : ℕ) ≤ n + r then h (n + r - i) else 0

/-- Critical low-to-high Jacobian, written directly as coefficients of the reciprocal response to
the monomial low-mode basis. -/
noncomputable def criticalReciprocalJacobian {K : Type*} [CommRing K]
    (Y : K[X]) (n m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun r i => (criticalReciprocalInfinitesimal Y (X ^ (i : ℕ))).coeff (n + r)

/-- Each Jacobian entry is the negative corresponding Toeplitz coefficient of `Y^(2 : ℕ)`. -/
theorem criticalReciprocalJacobian_apply {K : Type*} [CommRing K]
    (Y : K[X]) (n m : ℕ) (r i : Fin m) :
    criticalReciprocalJacobian Y n m r i =
      -rectangularSchurToeplitz (fun k => (Y * Y).coeff k) n m r i := by
  simp only [criticalReciprocalJacobian, criticalReciprocalInfinitesimal,
    coeff_neg, rectangularSchurToeplitz]
  rw [coeff_mul_X_pow']

/-- The complete critical Jacobian is the negative rectangular Schur Toeplitz matrix. -/
theorem criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz
    {K : Type*} [CommRing K] (Y : K[X]) (n m : ℕ) :
    criticalReciprocalJacobian Y n m =
      -rectangularSchurToeplitz (fun k => (Y * Y).coeff k) n m := by
  ext r i
  exact criticalReciprocalJacobian_apply Y n m r i

/-- The critical caustic determinant is, up to the universal sign, the rectangular
Jacobi--Trudi determinant of the squared reciprocal jet. -/
theorem criticalReciprocalJacobian_det_eq_rectangularSchur
    {K : Type*} [CommRing K] (Y : K[X]) (n m : ℕ) :
    (criticalReciprocalJacobian Y n m).det =
      (-1 : K) ^ m *
        (rectangularSchurToeplitz (fun k => (Y * Y).coeff k) n m).det := by
  rw [criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz]
  simpa using (Matrix.det_neg
    (rectangularSchurToeplitz (fun k => (Y * Y).coeff k) n m))

end GaloisForLFunctions.HTGeometry
