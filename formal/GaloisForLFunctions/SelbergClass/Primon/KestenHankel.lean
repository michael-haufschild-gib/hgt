import GaloisForLFunctions.SelbergClass.Primon.KestenJacobiMoments
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact prime phase Hankel determinants

The monic prime polynomials give a unitriangular coefficient change from
monomials. Their Gram matrix is diagonal with entries `1, 1+p⁻¹, 1+p⁻¹, …`.
Thus the size-`n+1` Hankel determinant of the actual phase moments is
`(1+p⁻¹)ⁿ`, and every finite Hankel section is strictly positive definite.
-/

open Polynomial HTGeometry Matrix

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Columns are the monomial coefficients of the successive monic prime polynomials. -/
def kestenCoefficientMatrix (p : Nat.Primes) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (kestenPolynomial p (j : ℕ)).coeff (i : ℕ)

/-- Monicity makes the change of polynomial coordinates unimodular. -/
theorem det_kestenCoefficientMatrix (p : Nat.Primes) (N : ℕ) :
    (kestenCoefficientMatrix p N).det = 1 := by
  exact Matrix.det_matrixOfPolynomials (fun i : Fin N => kestenPolynomial p i)
    (fun i => kestenPolynomial_natDegree p i) (fun i => kestenPolynomial_monic p i)

private theorem kestenPolynomial_expansion (p : Nat.Primes) (N : ℕ) (i : Fin N) :
    kestenPolynomial p i =
      ∑ k : Fin N, Polynomial.monomial (k : ℕ) ((kestenPolynomial p i).coeff k) := by
  exact ((kestenPolynomial p i).as_sum_range' N (by
    rw [kestenPolynomial_natDegree]
    exact i.isLt)).trans
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ => Polynomial.monomial k ((kestenPolynomial p i).coeff k)) N).symm

/-- The finite polynomial coefficient change diagonalizes the actual moment Hankel matrix. -/
theorem kesten_hankel_congruence (p : Nat.Primes) (N : ℕ) :
    (kestenCoefficientMatrix p N).transpose * momentHankelMatrix (kestenMoment p) N *
      kestenCoefficientMatrix p N =
        Matrix.diagonal (fun i : Fin N => if (i : ℕ) = 0 then 1 else 1 + (p : ℝ)⁻¹) := by
  ext i j
  have he : ((kestenCoefficientMatrix p N).transpose * momentHankelMatrix (kestenMoment p) N *
      kestenCoefficientMatrix p N) i j =
      momentInner (kestenMoment p) (kestenPolynomial p i) (kestenPolynomial p j) := by
    rw [kestenPolynomial_expansion p N i, kestenPolynomial_expansion p N j,
      momentInner_sum_left]
    simp_rw [momentInner_sum_right, momentInner_def,
      Polynomial.monomial_mul_monomial, momentFunctional_monomial]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, kestenCoefficientMatrix,
      momentHankelMatrix, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, momentInner_kestenPolynomial, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j
    simp
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun hv => h (Fin.ext hv)
    simp [h, hv]

/-- Every finite prime phase Hankel section is strictly positive definite. -/
theorem kestenMoment_hankel_posDef (p : Nat.Primes) (N : ℕ) :
    (momentHankelMatrix (kestenMoment p) N).PosDef :=
  positiveMomentForm_iff_momentHankelMatrix_posDef.mp (kestenMoment_positiveMomentForm p) N

/-- The complete determinant sequence has a closed geometric form. -/
theorem det_kestenMoment_hankel_succ (p : Nat.Primes) (n : ℕ) :
    (momentHankelMatrix (kestenMoment p) (n + 1)).det = (1 + (p : ℝ)⁻¹) ^ n := by
  have h := congrArg Matrix.det (kesten_hankel_congruence p (n + 1))
  simp only [Matrix.det_mul, Matrix.det_transpose,
    det_kestenCoefficientMatrix, one_mul, mul_one, Matrix.det_diagonal] at h
  calc
    (momentHankelMatrix (kestenMoment p) (n + 1)).det =
        ∏ i : Fin (n + 1), if (i : ℕ) = 0 then 1 else 1 + (p : ℝ)⁻¹ := h
    _ = ∏ i ∈ Finset.range (n + 1), if i = 0 then 1 else 1 + (p : ℝ)⁻¹ :=
      Fin.prod_univ_eq_prod_range (fun i : ℕ => if i = 0 then 1 else 1 + (p : ℝ)⁻¹) _
    _ = (1 + (p : ℝ)⁻¹) ^ n := by rw [Finset.prod_range_succ']; simp

/-- No finite prime phase Hankel determinant vanishes. -/
theorem det_kestenMoment_hankel_pos (p : Nat.Primes) (N : ℕ) :
    0 < (momentHankelMatrix (kestenMoment p) N).det := by
  cases N with
  | zero => simp
  | succ n =>
    rw [det_kestenMoment_hankel_succ]
    positivity

end
end GaloisForLFunctions.SelbergClass.Primon
