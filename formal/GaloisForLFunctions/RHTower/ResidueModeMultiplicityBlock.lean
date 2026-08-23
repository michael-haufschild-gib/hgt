import GaloisForLFunctions.HTGeometry.TriangularCoefficientInjectivity
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Multiplicity blocks of finite residue modes

An order-`m+1` pole contributes a polynomial of degree `m` in `t-s`.  This file expands the
literal bivariate polynomial, identifies its coefficient matrix, and proves that a nonzero top
Laurent coefficient makes this anti-triangular matrix have exact rank `m+1`.  Thus every mode in
the exponential-polynomial block occurs.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

open Polynomial

/-- Polynomial in `t`, with coefficients polynomial in `s`, equal to
`sum_k a_k (t-s)^k`. -/
def residueModeBivariatePolynomial (m : ℕ) (a : Fin (m + 1) → ℂ) :
    Polynomial (Polynomial ℂ) :=
  ∑ k : Fin (m + 1),
    Polynomial.C (Polynomial.C (a k)) *
      (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial ℂ)) ^ k.val

/-- The literal exponential-polynomial residue kernel before the common exponential factor. -/
def residueModeKernelPolynomial (m : ℕ) (a : Fin (m + 1) → ℂ) (t s : ℂ) : ℂ :=
  ∑ k : Fin (m + 1), a k * (t - s) ^ k.val

theorem residueModeBivariatePolynomial_eval₂ (m : ℕ) (a : Fin (m + 1) → ℂ)
    (t s : ℂ) :
    Polynomial.eval₂ (Polynomial.evalRingHom s) t (residueModeBivariatePolynomial m a) =
      residueModeKernelPolynomial m a t s := by
  rw [residueModeBivariatePolynomial, residueModeKernelPolynomial,
    Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp

/-- Coefficient of `t^r s^q` in `sum_k a_k (t-s)^k`, truncated at degree `m`. -/
def residueModeCoeffMatrix (m : ℕ) (a : Fin (m + 1) → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun r q =>
    if h : r.val + q.val ≤ m then
      a ⟨r.val + q.val, by omega⟩ * (Nat.choose (r.val + q.val) q.val : ℂ) *
        (-1 : ℂ) ^ q.val
    else 0

theorem coeff_neg_X_pow (n q : ℕ) :
    ((-Polynomial.X : Polynomial ℂ) ^ n).coeff q =
      if n = q then (-1 : ℂ) ^ n else 0 := by
  have hneg : (-Polynomial.X : Polynomial ℂ) =
      Polynomial.C (-1 : ℂ) * Polynomial.X := by simp
  rw [hneg, mul_pow, ← map_pow, Polynomial.coeff_C_mul_X_pow]
  simp [eq_comm]

/-- The matrix is exactly the iterated coefficient array of the bivariate residue polynomial. -/
theorem residueModeBivariatePolynomial_coeff_coeff
    (m : ℕ) (a : Fin (m + 1) → ℂ) (r q : Fin (m + 1)) :
    ((residueModeBivariatePolynomial m a).coeff r.val).coeff q.val =
      residueModeCoeffMatrix m a r q := by
  rw [residueModeBivariatePolynomial, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul]
  simp only [sub_eq_add_neg, ← map_neg, Polynomial.coeff_X_add_C_pow]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, ← Polynomial.C_eq_natCast,
    Polynomial.coeff_mul_C, coeff_neg_X_pow]
  by_cases hle : r.val + q.val ≤ m
  · let b : Fin (m + 1) := ⟨r.val + q.val, by omega⟩
    rw [Finset.sum_eq_single b]
    · simp [b, residueModeCoeffMatrix, hle]
      rw [Nat.choose_symm_add]
      ring
    · intro x _ hxb
      by_cases hrx : r.val ≤ x.val
      · have hdiff : x.val - r.val ≠ q.val := by
          intro heq
          apply hxb
          apply Fin.ext
          simp only [b]
          omega
        simp [hdiff]
      · have hchoose : Nat.choose x.val r.val = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hchoose]
    · simp
  · rw [residueModeCoeffMatrix, dif_neg hle]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hrx : r.val ≤ x.val
    · have hdiff : x.val - r.val ≠ q.val := by
        intro heq
        apply hle
        have hx : x.val ≤ m := Nat.le_of_lt_succ x.isLt
        omega
      simp [hdiff]
    · have hchoose : Nat.choose x.val r.val = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [hchoose]

/-- Reversing output degrees turns the anti-triangular coefficient matrix into a lower triangle. -/
def residueModeRowReversedMatrix (m : ℕ) (a : Fin (m + 1) → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun r q => residueModeCoeffMatrix m a (Fin.rev r) q

theorem residueModeRowReversedMatrix_lowerTriangular (m : ℕ) (a : Fin (m + 1) → ℂ)
    (r q : Fin (m + 1)) (hrq : r < q) :
    residueModeRowReversedMatrix m a r q = 0 := by
  have hrev : (Fin.rev r).val = m - r.val := by
    simp [Fin.rev]
  rw [residueModeRowReversedMatrix, residueModeCoeffMatrix]
  simp only [hrev]
  split_ifs with h
  · omega
  · rfl

theorem residueModeRowReversedMatrix_diagonal (m : ℕ) (a : Fin (m + 1) → ℂ)
    (r : Fin (m + 1)) :
    residueModeRowReversedMatrix m a r r =
      a (Fin.last m) * (Nat.choose m r.val : ℂ) * (-1 : ℂ) ^ r.val := by
  have hrev : (Fin.rev r).val = m - r.val := by
    simp [Fin.rev]
  have hsum : m - r.val + r.val = m := by omega
  rw [residueModeRowReversedMatrix, residueModeCoeffMatrix]
  simp only [hrev]
  rw [dif_pos (by omega : m - r.val + r.val ≤ m)]
  have hindex :
      (⟨m - r.val + r.val, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    exact hsum
  rw [hindex, hsum]

theorem residueModeRowReversedMatrix_diagonal_ne_zero
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0)
    (r : Fin (m + 1)) : residueModeRowReversedMatrix m a r r ≠ 0 := by
  rw [residueModeRowReversedMatrix_diagonal]
  refine mul_ne_zero (mul_ne_zero ha ?_) (pow_ne_zero _ (by norm_num))
  exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt_succ r.isLt)

theorem residueModeRowReversedMatrix_det_ne_zero
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0) :
    (residueModeRowReversedMatrix m a).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _
    (residueModeRowReversedMatrix_lowerTriangular m a)]
  exact Finset.prod_ne_zero_iff.mpr fun r _ =>
    residueModeRowReversedMatrix_diagonal_ne_zero m a ha r

theorem residueModeRowReversedMatrix_mulVec_injective
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0) :
    Function.Injective (residueModeRowReversedMatrix m a).mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact residueModeRowReversedMatrix_det_ne_zero m a ha

theorem residueModeCoeffMatrix_mulVec_injective
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0) :
    Function.Injective (residueModeCoeffMatrix m a).mulVec := by
  intro x y hxy
  apply residueModeRowReversedMatrix_mulVec_injective m a ha
  funext r
  simpa [residueModeRowReversedMatrix, Matrix.mulVec] using congrFun hxy (Fin.rev r)

/-- A nonzero top Laurent coefficient produces all `m+1` residue modes. -/
theorem residueModeCoeffMatrix_rank
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0) :
    (residueModeCoeffMatrix m a).rank = m + 1 := by
  have hunit : IsUnit (residueModeCoeffMatrix m a) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (residueModeCoeffMatrix_mulVec_injective m a ha)
  simpa using Matrix.rank_of_isUnit (residueModeCoeffMatrix m a) hunit

end

end RHTower
