import GaloisForLFunctions.HTGeometry.EvaluationCodimensionCore
import GaloisForLFunctions.HTGeometry.DisjointBlockPolynomialIndependence

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- The row equation in jet variables associated with a coefficient tensor and one evaluation
base. -/
def coefficientRowPolynomial
    {κ σ : Type*} [Fintype κ] (q : ℕ) (exponent : κ → (σ →₀ ℕ))
    (c : κ × Fin (q + 1) → ℂ) (z : ℂ) : MvPolynomial σ ℂ :=
  ∑ a, MvPolynomial.monomial (exponent a) (∑ d, c (a, d) * z ^ (d : ℕ))

/-- Distinct monomial exponents recover each coefficient polynomial exactly. -/
@[simp] theorem coefficientRowPolynomial_coeff
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    (q : ℕ) (exponent : κ → (σ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (c : κ × Fin (q + 1) → ℂ) (z : ℂ) (a : κ) :
    (coefficientRowPolynomial q exponent c z).coeff (exponent a) =
      ∑ d, c (a, d) * z ^ (d : ℕ) := by
  classical
  rw [coefficientRowPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  simp [hexponent.eq_iff]

/-- A row carrying a nonzero coefficient polynomial gives a nonzero jet polynomial. -/
theorem coefficientRowPolynomial_ne_zero
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    (q : ℕ) (exponent : κ → (σ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (c : κ × Fin (q + 1) → ℂ) (z : ℂ)
    (hgood : ∃ a, ∑ d, c (a, d) * z ^ (d : ℕ) ≠ 0) :
    coefficientRowPolynomial q exponent c z ≠ 0 := by
  obtain ⟨a, ha⟩ := hgood
  intro hzero
  have hcoeff : (coefficientRowPolynomial q exponent c z).coeff (exponent a) = 0 := by
    rw [hzero]
    simp
  rw [coefficientRowPolynomial_coeff q exponent hexponent] at hcoeff
  exact ha hcoeff

/-- Rows on which at least one bounded coefficient polynomial is nonzero. -/
def coefficientGoodRow
    {row κ : Type*} [Fintype κ]
    (q : ℕ) (z : row → ℂ) (c : κ × Fin (q + 1) → ℂ) :=
  {b : row // ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0}

noncomputable instance coefficientGoodRowFintype
    {row κ : Type*} [Fintype row] [Fintype κ]
    (q : ℕ) (z : row → ℂ) (c : κ × Fin (q + 1) → ℂ) :
    Fintype (coefficientGoodRow q z c) := by
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Root counting supplies at least `card row - q` good rows. -/
theorem coefficientGoodRow_card_lower
    {row κ : Type*} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (c : κ × Fin (q + 1) → ℂ) (hc : c ≠ 0) :
    Fintype.card row ≤ q + Fintype.card (coefficientGoodRow q z c) := by
  classical
  have h := card_rows_some_boundedCoefficientPolynomial_nonzero q z hz c hc
  unfold coefficientGoodRow
  rw [Fintype.card_subtype]
  simpa [coefficientGoodRow] using h

/-- A nonzero constant row polynomial has an empty zero locus. -/
theorem coefficientRowPolynomial_eval_ne_zero_of_constant
    {κ σ : Type*} [Fintype κ] [DecidableEq κ]
    (q : ℕ) (exponent : κ → (σ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (c : κ × Fin (q + 1) → ℂ) (z : ℂ)
    (hgood : ∃ a, ∑ d, c (a, d) * z ^ (d : ℕ) ≠ 0)
    (hconst : IsConstantMvPolynomial (coefficientRowPolynomial q exponent c z)) :
    ∀ x : σ → ℂ, MvPolynomial.eval x (coefficientRowPolynomial q exponent c z) ≠ 0 := by
  obtain ⟨a, ha⟩ := hconst
  have hpoly := coefficientRowPolynomial_ne_zero q exponent hexponent c z hgood
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hpoly
    rw [← ha, ha0, MvPolynomial.C_0]
  intro x
  rw [← ha, MvPolynomial.eval_C]
  exact ha0

/-- **Fixed-coefficient incidence-independence dichotomy.** For every nonzero bounded coefficient
tensor,
root counting supplies at least `card row - q` active row equations. Either one active equation is
a nonzero constant, so the incidence fiber is empty, or all active equations are nonconstant and,
after placement in disjoint row-variable blocks, are algebraically independent. -/
theorem coefficientIncidenceFiber_empty_or_algebraicIndependent
    {row κ σ : Type*} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (σ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (c : κ × Fin (q + 1) → ℂ) (hc : c ≠ 0) :
    Fintype.card row ≤ q + Fintype.card (coefficientGoodRow q z c) ∧
      ((∃ b : coefficientGoodRow q z c,
          ∀ x : σ → ℂ,
            MvPolynomial.eval x (coefficientRowPolynomial q exponent c (z b.1)) ≠ 0) ∨
        AlgebraicIndependent ℂ (fun b : coefficientGoodRow q z c =>
          rowBlockPolynomial b (coefficientRowPolynomial q exponent c (z b.1)))) := by
  classical
  refine ⟨coefficientGoodRow_card_lower q z hz c hc, ?_⟩
  by_cases hconst : ∃ b : coefficientGoodRow q z c,
      IsConstantMvPolynomial (coefficientRowPolynomial q exponent c (z b.1))
  · left
    obtain ⟨b, hb⟩ := hconst
    exact ⟨b, coefficientRowPolynomial_eval_ne_zero_of_constant
      q exponent hexponent c (z b.1) b.2 hb⟩
  · right
    apply rowBlockPolynomial_algebraicIndependent
    intro b hb
    exact hconst ⟨b, hb⟩

end
end GaloisForLFunctions.HTGeometry
