import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# Landau--Ginzburg Hessian and rank--level pairing duality

After fixing the raw tail, the reversed reciprocal packet is the gradient of the top logarithmic
coefficient of the raw polynomial.  Its Hessian is the symmetric Hankel form of `-Y^(2 : ℕ)`; reversing
the rows recovers the Schur--Toeplitz critical Jacobian.

The paper theorem also has a dual potential with the horizon depths exchanged.  This file verifies
the exact Hessian symmetry/reindexing and the polynomial top-pairing cancellation used to show that
the two critical values are negatives.  Formal power-series differentiation of the logarithmic
potential remains stated at paper level.
-/

open Polynomial
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Symmetric Hessian of the top logarithmic coefficient.  Coefficients below index zero are
represented by the zero branch. -/
noncomputable def criticalReciprocalHessian {K : Type*} [CommRing K]
    (Y : K[X]) (L m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun i j => if (i : ℕ) + j < L then
    -(Y * Y).coeff (L - 1 - ((i : ℕ) + j)) else 0

/-- The critical reciprocal Hessian is symmetric. -/
theorem criticalReciprocalHessian_transpose {K : Type*} [CommRing K]
    (Y : K[X]) (L m : ℕ) :
    (criticalReciprocalHessian Y L m)ᵀ = criticalReciprocalHessian Y L m := by
  ext i j
  simp [criticalReciprocalHessian, add_comm]

/-- Reversing the Hessian rows gives the low-to-high reciprocal Jacobian at `L=m+n`. -/
theorem criticalReciprocalJacobian_eq_reverseRows_hessian
    {K : Type*} [CommRing K] (Y : K[X]) (n m : ℕ) (r j : Fin m) :
    criticalReciprocalJacobian Y n m r j =
      criticalReciprocalHessian Y (m + n) m (Fin.rev r) j := by
  simp only [criticalReciprocalJacobian_apply, rectangularSchurToeplitz,
    criticalReciprocalHessian, Fin.val_rev]
  split_ifs with hleft hright
  · congr 2
    omega
  · omega
  · omega
  · simp

/-- Coefficient pairing at the top critical order. -/
noncomputable def criticalHorizonTopPairing {K : Type*} [CommSemiring K]
    (m n : ℕ) (A Q : K[X]) : K :=
  (A * Q).coeff (m + n - 1)

/-- The two source-tail linear pairings cancel on a compatible critical factorization.  The degree
bounds kill `A B` at top order, while the tail divisibilities kill `P Q` below order `m+n`. -/
theorem criticalHorizonTopPairing_add_dual_eq_zero
    {K : Type*} [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A B P Q : K[X]}
    (hA : A.natDegree < m) (hB : B.natDegree < n)
    (hP : X ^ m ∣ P) (hQ : X ^ n ∣ Q)
    (hcompat : ((A + P) * (B + Q)).coeff (m + n - 1) = 0) :
    criticalHorizonTopPairing m n A Q +
      criticalHorizonTopPairing m n B P = 0 := by
  have hABdeg : (A * B).natDegree < m + n - 1 := by
    apply lt_of_le_of_lt natDegree_mul_le
    omega
  have hAB : (A * B).coeff (m + n - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hABdeg
  have hPQdiv : X ^ (m + n) ∣ P * Q := by
    rw [pow_add]
    exact mul_dvd_mul hP hQ
  have hPQ : (P * Q).coeff (m + n - 1) = 0 :=
    (X_pow_dvd_iff.mp hPQdiv) _ (by omega)
  simp only [add_mul, mul_add, coeff_add] at hcompat
  rw [hAB, hPQ] at hcompat
  simpa [criticalHorizonTopPairing, mul_comm, add_comm, add_left_comm, add_assoc] using hcompat

end GaloisForLFunctions.HTGeometry
