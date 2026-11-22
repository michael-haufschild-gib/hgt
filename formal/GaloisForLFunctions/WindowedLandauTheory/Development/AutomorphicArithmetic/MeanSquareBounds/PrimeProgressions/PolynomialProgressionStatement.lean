import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevStatement

/-! Uniform relative estimates at a fixed polynomial scale in the modulus. -/

open Finset Complex

noncomputable section

namespace QH.PrimeProgressions

def PsiRelPolynomial : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M ≤ Real.log y →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))

def PsiRelPolynomialB (cA : ℝ) : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M ≤ Real.log y → cA * Real.sqrt (Real.log y) < Real.log M →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * Real.exp (-(c * Real.log y / Real.log M))

def PNTAPRelPolynomial : Prop :=
  ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M →
    ∃ e : Option (DirichletCharacter ℂ M × ℝ),
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2) ∧
      (e = none → ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), ¬ IsExcPair χ₁ β₁) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X

end QH.PrimeProgressions
