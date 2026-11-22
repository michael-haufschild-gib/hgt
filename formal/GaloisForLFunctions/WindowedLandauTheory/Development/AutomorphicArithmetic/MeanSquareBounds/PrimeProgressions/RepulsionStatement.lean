import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevStatement

/-! Near-one zero repulsion with a fixed logarithmic loss in the exceptional parameter. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

def DeuringHeilbronnMB : Prop :=
  ∃ (c₀ c₁ c₂ : ℝ) (B : ℕ), 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → β₁ < 1 →
    IsLZero χ ρ → 1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ B)) / Real.log ((M : ℝ) * T) ≤ 1 - ρ.re

def ZeroSumOfB : Prop := LogDensityM → DeuringHeilbronnMB → ZeroSum

end QH.PrimeProgressions
