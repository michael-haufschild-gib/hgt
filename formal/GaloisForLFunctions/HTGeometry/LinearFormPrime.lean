import GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Invertible linear substitutions and the primality of a linear form

A square matrix with a two-sided inverse substitutes its row forms for the variables and gives an
automorphism of the polynomial ring, the inverse matrix substituting back.  Automorphisms preserve
primality, and a variable is prime, so every row form of an invertible matrix is prime.

The form used below is `d` times one variable minus the sum of all of them, which is the linear
factor cutting out the hyperplane on which that variable equals the average.  It is the row of an
invertible matrix, hence prime.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **An invertible matrix substitutes into an automorphism of the polynomial ring.** -/
noncomputable def matrixAlgEquiv (M N : Matrix n n R) (hMN : M * N = 1) (hNM : N * M = 1) :
    MvPolynomial n R ≃ₐ[R] MvPolynomial n R :=
  AlgEquiv.ofAlgHom (MvPolynomial.bind₁ M.toMvPolynomial) (MvPolynomial.bind₁ N.toMvPolynomial)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.bind₁_X_right, ← Matrix.toMvPolynomial_mul, hNM,
        Matrix.toMvPolynomial_one]
      rfl)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.bind₁_X_right, ← Matrix.toMvPolynomial_mul, hMN,
        Matrix.toMvPolynomial_one]
      rfl)

theorem matrixAlgEquiv_X (M N : Matrix n n R) (hMN : M * N = 1) (hNM : N * M = 1) (i : n) :
    matrixAlgEquiv M N hMN hNM (MvPolynomial.X i) = M.toMvPolynomial i := by
  rw [matrixAlgEquiv, AlgEquiv.ofAlgHom_apply, MvPolynomial.bind₁_X_right]

/-- **A row form of an invertible matrix is prime.** -/
theorem prime_toMvPolynomial [IsDomain R] (M N : Matrix n n R) (hMN : M * N = 1) (hNM : N * M = 1)
    (i : n) : Prime (M.toMvPolynomial i) := by
  rw [← matrixAlgEquiv_X M N hMN hNM i]
  exact (MulEquiv.prime_iff (matrixAlgEquiv M N hMN hNM) (p := MvPolynomial.X i)).2
    MvPolynomial.X_prime


/-! ## The linear form cutting out the average hyperplane -/

section AverageForm

variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]

/-- The matrix whose zeroth row form is `d` times the zeroth variable minus the sum of all of them,
and whose other rows are the standard basis. -/
noncomputable def avgShearMatrix (K : Type*) [Field K] (d : ℕ) [NeZero d] :
    Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j =>
    if i = 0 then (d : K) * (if j = 0 then 1 else 0) - 1 else if i = j then 1 else 0

omit [CharZero K] in
theorem blockTriangular_avgShearMatrix :
    (avgShearMatrix K d).BlockTriangular id := by
  intro i j hji
  simp only [id] at hji
  rw [Fin.lt_def] at hji
  simp only [avgShearMatrix, Matrix.of_apply]
  have hi : i ≠ 0 := by
    rintro rfl
    simp only [Fin.val_zero] at hji
    omega
  rw [if_neg hi, if_neg (by rintro rfl; omega)]

omit [CharZero K] in
theorem det_avgShearMatrix : (avgShearMatrix K d).det = (d : K) - 1 := by
  rw [Matrix.det_of_upperTriangular blockTriangular_avgShearMatrix,
    Finset.prod_eq_single (0 : Fin d)]
  · simp [avgShearMatrix]
  · intro i _ hi
    simp [avgShearMatrix, if_neg hi]
  · intro hcon
    exact absurd (Finset.mem_univ (0 : Fin d)) hcon

theorem isUnit_det_avgShearMatrix (hd : 2 ≤ d) :
    IsUnit (avgShearMatrix K d).det := by
  rw [det_avgShearMatrix]
  refine isUnit_iff_ne_zero.2 fun hcon => ?_
  have h1 : ((d : ℕ) : K) = ((1 : ℕ) : K) := by
    rw [Nat.cast_one]
    exact sub_eq_zero.1 hcon
  have := Nat.cast_injective (R := K) h1
  omega

/-- **The average form is prime.**  It is the zeroth row form of an invertible matrix. -/
theorem prime_avgShearMatrix_toMvPolynomial (hd : 2 ≤ d) :
    Prime ((avgShearMatrix K d).toMvPolynomial 0) :=
  prime_toMvPolynomial _ _ (Matrix.mul_nonsing_inv _ (isUnit_det_avgShearMatrix hd))
    (Matrix.nonsing_inv_mul _ (isUnit_det_avgShearMatrix hd)) 0

omit [CharZero K] in
/-- **The average form written out.** -/
theorem avgShearMatrix_toMvPolynomial_zero :
    (avgShearMatrix K d).toMvPolynomial 0 =
      (d : MvPolynomial (Fin d) K) * MvPolynomial.X 0 - ∑ j : Fin d, MvPolynomial.X j := by
  have hentry : ∀ j : Fin d, (avgShearMatrix K d) 0 j = (if j = 0 then (d : K) else 0) - 1 := by
    intro j
    by_cases hj : j = 0
    · simp [avgShearMatrix, hj]
    · simp [avgShearMatrix, hj]
  have hterm : ∀ j : Fin d,
      (MvPolynomial.monomial (Finsupp.single j 1) ((avgShearMatrix K d) 0 j) :
        MvPolynomial (Fin d) K) =
        (if j = 0 then (d : MvPolynomial (Fin d) K) * MvPolynomial.X j else 0) -
          MvPolynomial.X j := by
    intro j
    rw [← MvPolynomial.C_mul_X_eq_monomial, hentry j, map_sub, MvPolynomial.C_1, sub_mul, one_mul]
    congr 1
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos hj]
      congr 1
    · rw [if_neg hj, if_neg hj, map_zero, zero_mul]
  rw [Matrix.toMvPolynomial, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin d)
      (fun j => (d : MvPolynomial (Fin d) K) * MvPolynomial.X j),
    if_pos (Finset.mem_univ _)]

end AverageForm

end GaloisForLFunctions.HTGeometry
