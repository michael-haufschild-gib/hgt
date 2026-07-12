import GaloisForLFunctions.DifferentialIndependence
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Full-row-rank linear forms preserve algebraic independence

If a coefficient matrix has a right inverse, substitution by its row linear forms has a left
inverse on multivariate polynomial rings.  Hence those linear forms in an algebraically independent
family remain algebraically independent.  This is the nonlinear-rank core used to pass from
polynomial differential-operator row rank to differential transcendence rank.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial

noncomputable section

/-- Row linear forms of a matrix, evaluated in an algebra over the coefficient ring. -/
def matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) : A :=
  ∑ j, algebraMap R A (M i j) * x j

theorem aeval_toMvPolynomial_eq_matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) :
    MvPolynomial.aeval x (M.toMvPolynomial i) = matrixLinearForms M x i := by
  simp [Matrix.toMvPolynomial, matrixLinearForms, MvPolynomial.aeval_def]

/-- A right-invertible row transformation preserves algebraic independence. -/
theorem algebraicIndependent_matrixLinearForms_of_mul_eq_one
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (N : Matrix n m R) (hMN : M * N = 1)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  rw [algebraicIndependent_iff]
  intro p hp
  let q : MvPolynomial n R := MvPolynomial.bind₁ M.toMvPolynomial p
  have hqeval : MvPolynomial.aeval x q = 0 := by
    dsimp [q]
    rw [MvPolynomial.aeval_bind₁]
    simpa only [aeval_toMvPolynomial_eq_matrixLinearForms] using hp
  have hq : q = 0 := hx.eq_zero_of_aeval_eq_zero q hqeval
  have hundone : MvPolynomial.bind₁ N.toMvPolynomial q = p := by
    dsimp [q]
    rw [MvPolynomial.bind₁_bind₁]
    have hvar : (fun i => MvPolynomial.bind₁ N.toMvPolynomial (M.toMvPolynomial i)) =
        (MvPolynomial.X : m → MvPolynomial m R) := by
      funext i
      rw [← Matrix.toMvPolynomial_mul, hMN, Matrix.toMvPolynomial_one]
    rw [hvar]
    exact AlgHom.congr_fun MvPolynomial.bind₁_X_left p
  rw [hq, map_zero] at hundone
  exact hundone.symm

/-- A matrix over a field with linearly independent rows has a right inverse. -/
theorem exists_matrix_rightInverse_of_linearIndependent_rows
    {R m n : Type*} [Field R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row) :
    ∃ N : Matrix n m R, M * N = 1 := by
  have hrank : M.rank = Fintype.card m := hM.rank_matrix
  have hrange : Module.finrank R (LinearMap.range M.mulVecLin) =
      Module.finrank R (m → R) := by
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrange
  have hsurj : Function.Surjective M.mulVec := by
    exact LinearMap.range_eq_top.mp htop
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj

/-- Linearly independent matrix rows evaluated on an algebraically independent family remain
algebraically independent. -/
theorem algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    {R A m n : Type*} [Field R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  obtain ⟨N, hMN⟩ := exists_matrix_rightInverse_of_linearIndependent_rows M hM
  exact algebraicIndependent_matrixLinearForms_of_mul_eq_one M N hMN x hx

end

end GaloisForLFunctions.HTGeometry
