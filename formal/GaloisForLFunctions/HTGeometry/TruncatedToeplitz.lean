import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Truncated Toeplitz matrices of a jet

The lower-triangular Toeplitz matrix of a polynomial, cut at the horizon, converts polynomial
multiplication into matrix multiplication:

```text
toeplitz L F               entry (k, i) is F_{k-i} for i ≤ k, and 0 otherwise
toeplitz_mul               ** T(F) · T(G) = T(F · G) **
det_toeplitz               det T(F) = (F.coeff 0) ^ L
toeplitz_one, toeplitz_congr_of_dvd
toeplitz_mul_toeplitz_of_inverse
    ** X^L ∣ F G - 1  ⟹  T(F) · T(G) = 1 **
isUnit_det_toeplitz_of_inverse
```

Multiplicativity is proved by reindexing the band `i ≤ j ≤ k` of the matrix product onto the
antidiagonal convolution.  Since only coefficients below the horizon enter, an inverse pair of jets
gives literally inverse matrices — which is what turns the Sylvester block of the critical
presentation differential into a block with an identity corner.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

variable {C : Type*} [CommRing C]

/-- The lower-triangular truncated Toeplitz matrix of a polynomial. -/
def toeplitz (L : ℕ) (F : C[X]) : Matrix (Fin L) (Fin L) C :=
  fun k i => if (i : ℕ) ≤ (k : ℕ) then F.coeff ((k : ℕ) - (i : ℕ)) else 0

theorem toeplitz_apply (L : ℕ) (F : C[X]) (k i : Fin L) :
    toeplitz L F k i = if (i : ℕ) ≤ (k : ℕ) then F.coeff ((k : ℕ) - (i : ℕ)) else 0 := rfl

/-- The determinant of a truncated Toeplitz matrix is a power of the constant term. -/
theorem det_toeplitz (L : ℕ) (F : C[X]) : (toeplitz L F).det = (F.coeff 0) ^ L := by
  classical
  rw [Matrix.det_of_lowerTriangular]
  · simp [toeplitz_apply]
  · intro i j hij
    rw [toeplitz_apply, if_neg]
    have hlt : (i : ℕ) < (j : ℕ) := hij
    omega

/-- **Multiplicativity of the truncated Toeplitz construction.** -/
theorem toeplitz_mul (L : ℕ) (F G : C[X]) :
    toeplitz L F * toeplitz L G = toeplitz L (F * G) := by
  classical
  ext k i
  rw [Matrix.mul_apply, toeplitz_apply]
  by_cases hik : (i : ℕ) ≤ (k : ℕ)
  · rw [if_pos hik, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin L)),
        j ∉ (Finset.univ : Finset (Fin L)).filter
          (fun j : Fin L => (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) ≤ (k : ℕ)) →
        toeplitz L F k j * toeplitz L G j i = 0 := by
      intro j _ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hj
      by_cases h1 : (i : ℕ) ≤ (j : ℕ)
      · rw [toeplitz_apply, if_neg (by have := hj h1; omega), zero_mul]
      · rw [toeplitz_apply (i := i), if_neg h1, mul_zero]
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
    refine (Finset.sum_bij' (i := fun a _ => (⟨(k : ℕ) - a, by omega⟩ : Fin L))
      (j := fun b _ => (k : ℕ) - (b : ℕ)) ?_ ?_ ?_ ?_ ?_).symm
    · intro a ha
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (i : ℕ) ≤ (k : ℕ) - a ∧ (k : ℕ) - a ≤ (k : ℕ)
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_range]
      omega
    · intro a ha
      simp only [Finset.mem_range] at ha
      show (k : ℕ) - ((k : ℕ) - a) = a
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      apply Fin.ext
      show (k : ℕ) - ((k : ℕ) - (b : ℕ)) = (b : ℕ)
      omega
    · intro a ha
      simp only [Finset.mem_range] at ha
      rw [toeplitz_apply, toeplitz_apply,
        if_pos (show (i : ℕ) ≤ (k : ℕ) - a by omega),
        if_pos (show ((k : ℕ) - a) ≤ (k : ℕ) by omega)]
      have h1 : (k : ℕ) - ((k : ℕ) - a) = a := by omega
      have h2 : ((k : ℕ) - a) - (i : ℕ) = (k : ℕ) - (i : ℕ) - a := by omega
      rw [show ((k : ℕ) - (⟨(k : ℕ) - a, by omega⟩ : Fin L) : ℕ) = a from h1,
        show ((⟨(k : ℕ) - a, by omega⟩ : Fin L) - (i : ℕ) : ℕ)
          = (k : ℕ) - (i : ℕ) - a from h2]
  · rw [if_neg hik]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : (i : ℕ) ≤ (j : ℕ)
    · rw [toeplitz_apply, if_neg (by omega), zero_mul]
    · rw [toeplitz_apply (i := i), if_neg h1, mul_zero]

theorem toeplitz_one (L : ℕ) : toeplitz L (1 : C[X]) = 1 := by
  classical
  ext k i
  rw [toeplitz_apply, Matrix.one_apply]
  by_cases hki : k = i
  · subst hki
    rw [if_pos le_rfl, Polynomial.coeff_one, if_pos (Nat.sub_self _), if_pos rfl]
  · by_cases h : (i : ℕ) ≤ (k : ℕ)
    · rw [if_pos h, Polynomial.coeff_one, if_neg, if_neg hki]
      intro hc
      exact hki (Fin.ext (by omega))
    · rw [if_neg h, if_neg hki]

/-- Only the coefficients below the horizon matter. -/
theorem toeplitz_congr_of_dvd (L : ℕ) {F G : C[X]} (h : (X : C[X]) ^ L ∣ F - G) :
    toeplitz L F = toeplitz L G := by
  ext k i
  rw [toeplitz_apply, toeplitz_apply]
  by_cases hik : (i : ℕ) ≤ (k : ℕ)
  · rw [if_pos hik, if_pos hik]
    have hc : (F - G).coeff ((k : ℕ) - (i : ℕ)) = 0 := by
      obtain ⟨t, ht⟩ := h
      rw [ht, Polynomial.coeff_X_pow_mul']
      simp only [ite_eq_right_iff]
      intro hle
      omega
    rw [Polynomial.coeff_sub, sub_eq_zero] at hc
    exact hc
  · rw [if_neg hik, if_neg hik]

/-- **Reciprocal jets give inverse Toeplitz matrices.**  If two polynomials multiply to one modulo
the horizon, their truncated Toeplitz matrices are mutually inverse. -/
theorem toeplitz_mul_toeplitz_of_inverse (L : ℕ) {F G : C[X]}
    (h : (X : C[X]) ^ L ∣ F * G - 1) : toeplitz L F * toeplitz L G = 1 := by
  rw [toeplitz_mul, toeplitz_congr_of_dvd L h, toeplitz_one]

/-- The truncated Toeplitz matrix of an invertible jet has unit determinant. -/
theorem isUnit_det_toeplitz_of_inverse (L : ℕ) {F G : C[X]}
    (h : (X : C[X]) ^ L ∣ F * G - 1) : IsUnit (toeplitz L F).det := by
  refine isUnit_iff_exists_inv.mpr ⟨(toeplitz L G).det, ?_⟩
  rw [← Matrix.det_mul, toeplitz_mul_toeplitz_of_inverse L h, Matrix.det_one]

end GaloisForLFunctions.HTGeometry
