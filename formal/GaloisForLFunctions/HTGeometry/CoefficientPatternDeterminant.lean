import GaloisForLFunctions.HTGeometry.ExpandedMonomialEvaluation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant polynomial for a coefficient-uniform differential pattern

For fixed evaluation bases, polynomial coefficient degrees, and jet monomials, the determinant of
the expanded evaluation matrix is itself a multivariate polynomial in all row-jet variables.  Its
nonvanishing is exactly the full-rank condition that excludes every coefficient vector of the
prescribed pattern simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Embed a jet exponent into the variables belonging to one evaluation row. -/
def rowEmbedding {row σ : Type*} (a : row) : σ ↪ row × σ :=
  ⟨fun i => (a, i), fun _ _ h => congrArg Prod.snd h⟩

/-- The copy of a jet monomial in one evaluation row. -/
noncomputable def rowJetMonomial
    {row σ : Type*} (a : row) (β : σ →₀ ℕ) :
    MvPolynomial (row × σ) ℂ :=
  MvPolynomial.monomial
    (Finsupp.embDomain (rowEmbedding a) β) 1

theorem eval_rowJetMonomial
    {row σ : Type*} (a : row) (β : σ →₀ ℕ)
    (y : row × σ → ℂ) :
    MvPolynomial.eval y (rowJetMonomial a β) =
      β.prod (fun i e => y (a, i) ^ e) := by
  classical
  rw [rowJetMonomial, MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_embDomain]
  rfl

/-- The determinant polynomial of the expanded coefficient-pattern evaluation matrix. -/
noncomputable def coefficientPatternDeterminant
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ)) :
    MvPolynomial (row × σ) ℂ :=
  (Matrix.of fun a b =>
    MvPolynomial.C (base a ^ degree b) * rowJetMonomial a (jetExponent b)).det

/-- Evaluation of the determinant polynomial is the determinant of the numerical expanded
monomial matrix. -/
theorem eval_coefficientPatternDeterminant
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ))
    (y : row × σ → ℂ) :
    MvPolynomial.eval y (coefficientPatternDeterminant base degree jetExponent) =
      (Matrix.of fun a b =>
        base a ^ degree b * (jetExponent b).prod (fun i e => y (a, i) ^ e) :
        Matrix row row ℂ).det := by
  rw [coefficientPatternDeterminant]
  change (MvPolynomial.eval y)
      (Matrix.det (Matrix.of fun a b =>
        MvPolynomial.C (base a ^ degree b) * rowJetMonomial a (jetExponent b))) = _
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [eval_rowJetMonomial]

/-- A single full-rank target packet certifies that the coefficient-pattern determinant polynomial
is nonzero. -/
theorem coefficientPatternDeterminant_ne_zero_of_isUnit
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ))
    (target : row × σ → ℂ)
    (hfull : IsUnit (Matrix.of fun a b =>
      base a ^ degree b * (jetExponent b).prod (fun i e => target (a, i) ^ e) :
      Matrix row row ℂ)) :
    coefficientPatternDeterminant base degree jetExponent ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval target) hzero
  rw [eval_coefficientPatternDeterminant] at heval
  have hdet : (Matrix.of fun a b =>
      base a ^ degree b * (jetExponent b).prod (fun i e => target (a, i) ^ e) :
      Matrix row row ℂ).det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hfull).ne_zero
  exact hdet (by simpa using heval)

end GaloisForLFunctions.HTGeometry
