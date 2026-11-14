import GaloisForLFunctions.HTGeometry.TruncatedToeplitz
import GaloisForLFunctions.RepresentationLifting.TruncatedResolution
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Periodic exactness for truncated Toeplitz matrices

The Toeplitz matrix of `Xᵏ` is multiplication by `xᵏ` in truncated coefficient
coordinates. Complementary powers therefore have matching images and kernels.
This realizes the periodic exactness used in Proposition 6.4 of
Ait Mohamed–El-Baz directly on the jet matrices.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix RepresentationLifting

variable {R : Type*} [CommRing R]

/-- A monomial Toeplitz matrix acts by the literal truncated coefficient shift. -/
theorem toeplitz_X_pow_mulVec (N k : ℕ) (v : Fin N → R) :
    (toeplitz N (X ^ k : R[X])).mulVec v = truncatedShift (R := R) N k v := by
  classical
  funext i
  rw [truncatedShift_apply]
  by_cases hk : k ≤ i.val
  · rw [dif_pos hk]
    let j : Fin N := ⟨i.val - k, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    change (∑ l : Fin N, toeplitz N (X ^ k : R[X]) i l * v l) = v j
    rw [Finset.sum_eq_single j]
    · have hj : j.val ≤ i.val := Nat.sub_le _ _
      have he : i.val - j.val = k := by dsimp [j]; omega
      simp only [toeplitz_apply, if_pos hj, coeff_X_pow, he, ite_true, one_mul]
    · intro l _ hlj
      by_cases hl : l.val ≤ i.val
      · have hne : i.val - l.val ≠ k := by
          intro he
          apply hlj
          apply Fin.ext
          dsimp [j]
          omega
        simp only [toeplitz_apply, if_pos hl, coeff_X_pow, if_neg hne, zero_mul]
      · simp only [toeplitz_apply, if_neg hl, zero_mul]
    · simp
  · rw [dif_neg hk]
    change (∑ l : Fin N, toeplitz N (X ^ k : R[X]) i l * v l) = 0
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l.val ≤ i.val
    · have hne : i.val - l.val ≠ k := by omega
      simp only [toeplitz_apply, if_pos hl, coeff_X_pow, if_neg hne, zero_mul]
    · simp only [toeplitz_apply, if_neg hl, zero_mul]

theorem toeplitz_X_pow_mulVecLin (N k : ℕ) :
    (toeplitz N (X ^ k : R[X])).mulVecLin = truncatedShift (R := R) N k := by
  apply LinearMap.ext
  exact toeplitz_X_pow_mulVec N k

/-- Exactness for every complementary pair of powers, over every commutative ring. -/
theorem toeplitz_X_pow_range_eq_ker (a b : ℕ) :
    LinearMap.range (toeplitz (a + b) (X ^ a : R[X])).mulVecLin =
      LinearMap.ker (toeplitz (a + b) (X ^ b : R[X])).mulVecLin := by
  rw [toeplitz_X_pow_mulVecLin, toeplitz_X_pow_mulVecLin]
  exact truncatedShift_range_eq_ker a b

/-- The kernel of multiplication by `X` is exactly the top coefficient line. -/
theorem toeplitz_X_socle (n : ℕ) :
    LinearMap.ker (toeplitz (n + 1) (X : R[X])).mulVecLin =
      LinearMap.range (toeplitz (n + 1) (X ^ n : R[X])).mulVecLin := by
  simpa only [pow_one] using (toeplitz_X_pow_range_eq_ker (R := R) n 1).symm

/-- The complementary exactness in the two-periodic resolution. -/
theorem toeplitz_X_top_kernel (n : ℕ) :
    LinearMap.ker (toeplitz (n + 1) (X ^ n : R[X])).mulVecLin =
      LinearMap.range (toeplitz (n + 1) (X : R[X])).mulVecLin := by
  have h := (toeplitz_X_pow_range_eq_ker (R := R) 1 n).symm
  rw [Nat.add_comm 1 n] at h
  simpa only [pow_one] using h

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.toeplitz_X_pow_range_eq_ker
