import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- A multivariate polynomial is constant exactly when it is a scalar polynomial. -/
def IsConstantMvPolynomial {σ : Type*} (P : MvPolynomial σ ℂ) : Prop :=
  ∃ a : ℂ, MvPolynomial.C a = P

/-- A nonconstant complex multivariate polynomial takes two different values. -/
theorem exists_mvPolynomial_eval_ne_of_not_constant
    {σ : Type*} {P : MvPolynomial σ ℂ} (hP : ¬ IsConstantMvPolynomial P) :
    ∃ x y : σ → ℂ, MvPolynomial.eval x P ≠ MvPolynomial.eval y P := by
  by_contra h
  push Not at h
  apply hP
  refine ⟨MvPolynomial.eval 0 P, ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [MvPolynomial.eval_C]
  exact (h x 0).symm

/-- Every nonconstant complex multivariate polynomial has an affine-line restriction of positive
degree. -/
theorem exists_mvPolynomial_line_natDegree_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℂ} (hP : ¬ IsConstantMvPolynomial P) :
    ∃ x y : σ → ℂ, (mvPolynomialLine P x y).natDegree ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := exists_mvPolynomial_eval_ne_of_not_constant hP
  refine ⟨x, y, ?_⟩
  intro hdeg
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  apply hxy
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) ha
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) ha
  rw [eval_mvPolynomialLine] at h0 h1
  simp at h0 h1
  exact h0.symm.trans h1

/-- The chosen positive-degree line restriction is transcendental over the coefficient field. -/
theorem exists_mvPolynomial_transcendental_line
    {σ : Type*} {P : MvPolynomial σ ℂ} (hP : ¬ IsConstantMvPolynomial P) :
    ∃ x y : σ → ℂ, Transcendental ℂ (mvPolynomialLine P x y) := by
  obtain ⟨x, y, hdeg⟩ := exists_mvPolynomial_line_natDegree_ne_zero hP
  refine ⟨x, y, Polynomial.transcendental _ hdeg ?_⟩
  rw [mem_nonZeroDivisors_iff]
  constructor <;> intro z hz
  · exact (mul_eq_zero.mp hz).resolve_left
      (Polynomial.leadingCoeff_ne_zero.mpr (fun hzero => hdeg (by simp [hzero])))
  · exact (mul_eq_zero.mp hz).resolve_right
      (Polynomial.leadingCoeff_ne_zero.mpr (fun hzero => hdeg (by simp [hzero])))

/-- Embed one row polynomial into its own variable block. -/
def rowBlockPolynomial {row σ : Type*} (b : row) (P : MvPolynomial σ ℂ) :
    MvPolynomial (row × σ) ℂ :=
  MvPolynomial.rename (Prod.mk b) P

/-- Simultaneous affine-line specialization of every row block. -/
def rowBlockLineSpecialization
    {row σ : Type*} (x y : row → σ → ℂ) :
    MvPolynomial (row × σ) ℂ →ₐ[ℂ] MvPolynomial row ℂ :=
  MvPolynomial.eval₂AlgHom ℂ (fun bs =>
    MvPolynomial.C (x bs.1 bs.2) +
      MvPolynomial.X bs.1 * MvPolynomial.C (y bs.1 bs.2 - x bs.1 bs.2))

/-- Specializing an embedded row block gives the corresponding univariate line polynomial in that
row's independent variable. -/
theorem rowBlockLineSpecialization_apply
    {row σ : Type*} (P : row → MvPolynomial σ ℂ)
    (x y : row → σ → ℂ) (b : row) :
    rowBlockLineSpecialization x y (rowBlockPolynomial b (P b)) =
      Polynomial.aeval (MvPolynomial.X b : MvPolynomial row ℂ)
        (mvPolynomialLine (P b) (x b) (y b)) := by
  change MvPolynomial.eval₂ _ _ (MvPolynomial.rename (Prod.mk b) (P b)) = _
  rw [MvPolynomial.eval₂_rename_prod_mk]
  unfold mvPolynomialLine
  rw [Polynomial.aeval_def]
  let φ : Polynomial ℂ →+* MvPolynomial row ℂ :=
    Polynomial.eval₂RingHom (algebraMap ℂ (MvPolynomial row ℂ)) (MvPolynomial.X b)
  change MvPolynomial.eval₂ _ _ (P b) =
    φ (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x b i) + Polynomial.X * Polynomial.C (y b i - x b i)) (P b))
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext a
    simp [φ]
  · funext i
    simp [φ]
  · rfl

/-- **Disjoint-block polynomial independence.** Any finite or infinite family of nonconstant
complex multivariate polynomials becomes algebraically independent after each polynomial is placed
in its own disjoint variable block. -/
theorem rowBlockPolynomial_algebraicIndependent
    {row σ : Type*} (P : row → MvPolynomial σ ℂ)
    (hP : ∀ b, ¬ IsConstantMvPolynomial (P b)) :
    AlgebraicIndependent ℂ (fun b => rowBlockPolynomial b (P b)) := by
  classical
  choose x y htrans using fun b => exists_mvPolynomial_transcendental_line (hP b)
  let Φ := rowBlockLineSpecialization x y
  apply AlgebraicIndependent.of_comp Φ
  have himage : (⇑Φ ∘ fun b => rowBlockPolynomial b (P b)) =
      fun b => Polynomial.aeval (MvPolynomial.X b : MvPolynomial row ℂ)
        (mvPolynomialLine (P b) (x b) (y b)) := by
    funext b
    exact rowBlockLineSpecialization_apply P x y b
  rw [himage]
  exact MvPolynomial.algebraicIndependent_polynomial_aeval_X
    (fun b => mvPolynomialLine (P b) (x b) (y b)) htrans

end
end GaloisForLFunctions.HTGeometry
