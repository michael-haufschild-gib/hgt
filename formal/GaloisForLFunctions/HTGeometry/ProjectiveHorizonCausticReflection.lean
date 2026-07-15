import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# Reflection parity of the rectangular horizon caustics

If a normalized reciprocal series is reflected by `t ↦ -t`, its coefficient sequence changes
from `h k` to `(-1)^k h k`.  The rectangular Toeplitz matrix is then obtained from the original
one by diagonal sign conjugation and the scalar `(-1)^n`.  Its determinant therefore has the
single weight sign `(-1)^(m*n)`.

For an analytic source satisfying `f(s)=f(1-s)`, this is the algebraic core of the exact law
`tau_(m,n)(1-s)=(-1)^(m*n) tau_(m,n)(s)`.  The analytic substitution is deliberately kept outside
this finite algebraic module.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient reflection is diagonal sign conjugation of every rectangular Toeplitz section. -/
theorem rectangularSchurToeplitz_reflection_eq_conjugate
    {K : Type*} [CommRing K] (h : ℕ → K) (n m : ℕ) :
    rectangularSchurToeplitz (fun k => (-1 : K) ^ k * h k) n m =
      (-1 : K) ^ n •
        (diagonal (fun r : Fin m => (-1 : K) ^ (r : ℕ)) *
          rectangularSchurToeplitz h n m *
          diagonal (fun i : Fin m => (-1 : K) ^ (i : ℕ))) := by
  ext r i
  rw [smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [rectangularSchurToeplitz]
  split_ifs with hri
  · have hsign :
        (-1 : K) ^ (n + (r : ℕ) - (i : ℕ)) =
          (-1 : K) ^ n * (-1 : K) ^ (r : ℕ) * (-1 : K) ^ (i : ℕ) := by
      calc
        (-1 : K) ^ (n + (r : ℕ) - (i : ℕ)) =
            (-1 : K) ^ ((n + (r : ℕ) - (i : ℕ)) + 2 * (i : ℕ)) := by
              simp [pow_add, pow_mul]
        _ = (-1 : K) ^ (n + (r : ℕ) + (i : ℕ)) := by
              congr 1
              omega
        _ = (-1 : K) ^ n * (-1 : K) ^ (r : ℕ) * (-1 : K) ^ (i : ℕ) := by
              simp [pow_add]
    rw [hsign]
    simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  · simp

/-- A rectangular caustic determinant is homogeneous of reflection parity `m*n`. -/
theorem rectangularSchurToeplitz_det_reflection
    {K : Type*} [CommRing K] (h : ℕ → K) (n m : ℕ) :
    (rectangularSchurToeplitz (fun k => (-1 : K) ^ k * h k) n m).det =
      (-1 : K) ^ (m * n) * (rectangularSchurToeplitz h n m).det := by
  rw [rectangularSchurToeplitz_reflection_eq_conjugate]
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  simp only [Fintype.card_fin]
  have hdiag :
      (∏ i : Fin m, (-1 : K) ^ (i : ℕ)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp [← pow_mul]
  have hpows : ((-1 : K) ^ n) ^ m = (-1 : K) ^ (m * n) := by
    rw [← pow_mul, Nat.mul_comm]
  calc
    ((-1 : K) ^ n) ^ m *
          ((∏ i : Fin m, (-1 : K) ^ (i : ℕ)) *
            (rectangularSchurToeplitz h n m).det *
            ∏ i : Fin m, (-1 : K) ^ (i : ℕ)) =
        (-1 : K) ^ (m * n) *
          ((∏ i : Fin m, (-1 : K) ^ (i : ℕ)) ^ 2 *
            (rectangularSchurToeplitz h n m).det) := by
              rw [hpows]
              ring
    _ = (-1 : K) ^ (m * n) * (rectangularSchurToeplitz h n m).det := by
      rw [hdiag, one_mul]

end GaloisForLFunctions.HTGeometry
