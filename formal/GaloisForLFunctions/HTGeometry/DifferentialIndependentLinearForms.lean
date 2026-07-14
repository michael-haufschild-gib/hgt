import GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms

/-!
# Constant linear changes of differentially independent families

An invertible constant linear recombination acts by the same matrix on every jet order.  This file
proves directly, by constructing the inverse substitution on the full countable jet polynomial
ring, that a full-row-rank recombination of a differentially independent finite family remains
differentially independent.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial GaloisForLFunctions

noncomputable section

/-- The formal linear combination at one index and one jet order. -/
def jetwiseMatrixLinearPolynomial
    {C m n : Type*} [CommRing C] [Fintype n]
    (M : Matrix m n C) (p : m × ℕ) : MvPolynomial (n × ℕ) C :=
  ∑ j, MvPolynomial.C (M p.1 j) * MvPolynomial.X (j, p.2)

/-- The corresponding linear combination of a family indexed by variable and jet order. -/
def jetwiseMatrixLinearForms
    {C A m n : Type*} [CommRing C] [CommRing A] [Algebra C A] [Fintype n]
    (M : Matrix m n C) (x : n × ℕ → A) (p : m × ℕ) : A :=
  ∑ j, algebraMap C A (M p.1 j) * x (j, p.2)

theorem aeval_jetwiseMatrixLinearPolynomial
    {C A m n : Type*} [CommRing C] [CommRing A] [Algebra C A] [Fintype n]
    (M : Matrix m n C) (x : n × ℕ → A) (p : m × ℕ) :
    MvPolynomial.aeval x (jetwiseMatrixLinearPolynomial M p) =
      jetwiseMatrixLinearForms M x p := by
  simp [jetwiseMatrixLinearPolynomial, jetwiseMatrixLinearForms]

/-- A right inverse to the coefficient matrix gives a left inverse on every formal jet variable. -/
theorem bind_jetwiseMatrixLinearPolynomial
    {C m n : Type*} [CommRing C] [Fintype m] [Fintype n]
    [DecidableEq m]
    (M : Matrix m n C) (N : Matrix n m C) (hMN : M * N = 1)
    (p : m × ℕ) :
    MvPolynomial.bind₁ (jetwiseMatrixLinearPolynomial N)
        (jetwiseMatrixLinearPolynomial M p) = MvPolynomial.X p := by
  rcases p with ⟨i, k⟩
  simp only [jetwiseMatrixLinearPolynomial, map_sum, map_mul,
    MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ j, ∑ l, MvPolynomial.C (M i l) *
        (MvPolynomial.C (N l j) * X (j, k)) =
        ∑ j, MvPolynomial.C ((M * N) i j) * X (j, k) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          rw [map_mul]
          ring
    _ = X (i, k) := by
      rw [hMN]
      simp [Matrix.one_apply]

/-- A right-invertible row transformation preserves algebraic independence simultaneously at all
jet orders. -/
theorem algebraicIndependent_jetwiseMatrixLinearForms_of_mul_eq_one
    {C A m n : Type*} [CommRing C] [CommRing A] [Algebra C A]
    [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n C) (N : Matrix n m C) (hMN : M * N = 1)
    (x : n × ℕ → A) (hx : AlgebraicIndependent C x) :
    AlgebraicIndependent C (jetwiseMatrixLinearForms M x) := by
  rw [algebraicIndependent_iff]
  intro p hp
  let q : MvPolynomial (n × ℕ) C :=
    MvPolynomial.bind₁ (jetwiseMatrixLinearPolynomial M) p
  have hqeval : MvPolynomial.aeval x q = 0 := by
    dsimp [q]
    rw [MvPolynomial.aeval_bind₁]
    simpa only [aeval_jetwiseMatrixLinearPolynomial] using hp
  have hq : q = 0 := hx.eq_zero_of_aeval_eq_zero q hqeval
  have hundone :
      MvPolynomial.bind₁ (jetwiseMatrixLinearPolynomial N) q = p := by
    dsimp [q]
    rw [MvPolynomial.bind₁_bind₁]
    have hvar :
        (fun i => MvPolynomial.bind₁ (jetwiseMatrixLinearPolynomial N)
          (jetwiseMatrixLinearPolynomial M i)) =
          (MvPolynomial.X : m × ℕ → MvPolynomial (m × ℕ) C) := by
      funext i
      exact bind_jetwiseMatrixLinearPolynomial M N hMN i
    rw [hvar]
    exact AlgHom.congr_fun MvPolynomial.bind₁_X_left p
  rw [hq, map_zero] at hundone
  exact hundone.symm

/-- Differentiating a constant matrix linear form applies the same matrix to every jet order. -/
theorem differentialJet_matrixLinearForms
    {C K m n : Type*} [CommRing C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype n]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (M : Matrix m n C) (x : n → K) (i : m) (r : ℕ) :
    differentialJet r (matrixLinearForms M x i) =
      matrixLinearForms M (fun j => differentialJet r (x j)) i := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [differentialJet_succ, ih]
      simp only [matrixLinearForms, map_sum, Derivation.leibniz, hconst,
        smul_eq_mul, mul_zero, add_zero]

/-- A right-invertible constant row transformation preserves differential algebraic independence. -/
theorem differentialIndependent_matrixLinearForms_of_mul_eq_one
    {C K m n : Type*} [CommRing C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype m] [Fintype n] [DecidableEq m]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (M : Matrix m n C) (N : Matrix n m C) (hMN : M * N = 1)
    (x : n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) := by
  unfold DifferentialIndependent at hx ⊢
  have h := algebraicIndependent_jetwiseMatrixLinearForms_of_mul_eq_one M N hMN
    (fun p : n × ℕ => differentialJet p.2 (x p.1)) hx
  have heq :
      (fun p : m × ℕ => differentialJet p.2 (matrixLinearForms M x p.1)) =
        jetwiseMatrixLinearForms M
          (fun p : n × ℕ => differentialJet p.2 (x p.1)) := by
    funext p
    exact differentialJet_matrixLinearForms hconst M x p.1 p.2
  rw [heq]
  exact h

/-- Full-row-rank constant linear recombination preserves differential independence. -/
theorem differentialIndependent_matrixLinearForms_of_linearIndependent_rows
    {C K m n : Type*} [Field C] [CommRing K] [Algebra C K]
    [Differential K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (M : Matrix m n C) (hM : LinearIndependent C M.row)
    (x : n → K) (hx : DifferentialIndependent C x) :
    DifferentialIndependent C (matrixLinearForms M x) := by
  obtain ⟨N, hMN⟩ := exists_matrix_rightInverse_of_linearIndependent_rows M hM
  exact differentialIndependent_matrixLinearForms_of_mul_eq_one hconst M N hMN x hx

end

end GaloisForLFunctions.HTGeometry
