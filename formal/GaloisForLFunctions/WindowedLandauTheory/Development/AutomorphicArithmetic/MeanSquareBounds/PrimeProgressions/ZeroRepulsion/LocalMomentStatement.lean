import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! The local logarithmic derivative expansions used in zero repulsion. -/

open Finset Complex
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

def DHCauchyFor (A : ℝ) : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ), 0 < r → 2 ≤ B →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, m ρ = analyticOrderNatAt f ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ A * Real.log B ∧
      ∀ (k : ℕ) (s : ℂ), s ∈ Metric.closedBall z₀ (r / 12) → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
          + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ A * Real.log B / r * (12 / r) ^ k

def DHCauchy : Prop := ∃ A : ℝ, 0 < A ∧ DHCauchyFor A

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ ‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, m ρ = analyticOrderNatAt ψ.LFunction ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
          - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
          + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

def DHLocal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ), DHLocalAt C M ψ t

end QH.PrimeProgressions
