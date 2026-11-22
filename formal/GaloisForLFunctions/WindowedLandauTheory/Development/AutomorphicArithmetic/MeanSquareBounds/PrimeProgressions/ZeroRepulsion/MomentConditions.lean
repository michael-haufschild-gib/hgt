import GaloisForLFunctions.RHTower.SiegelZeroFree
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.LocalMomentStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RepulsionPositivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RepulsionStatement

/-! Moment bounds used to turn finite power sums into an exceptional-zero repulsion estimate. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

def DHTuran2 : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 < C ∧ 1 ≤ A ∧ ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + A * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (A * n) ≤ ‖∑ i, z i ^ k‖

def DHIneqF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      (∑ i, 1 / w i).re ≤ 2 * (1 - β₁) / η ^ 2 + C * Real.log ((M : ℝ) * T) * 25 ∧
      ∀ j : ℕ, 1 ≤ j →
        ‖∑ i, 1 / (w i) ^ j‖ ≤
          ((-1 : ℂ) ^ (j - 1) * (iteratedDeriv (j - 1) (negLD (1 : DirichletCharacter ℂ M)) ((1 + η : ℝ) : ℂ)
              + iteratedDeriv (j - 1) (negLD χ₁) ((1 + η : ℝ) : ℂ))).re / ((j - 1).factorial : ℝ)
          + 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j

def DHHyper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (y x : ℝ), 3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
    1 ≤ y → y ≤ x →
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
      ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y) + C * M * (Real.log y + 1) / Real.sqrt y

def DHPrime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ σ : ℝ) (k : ℕ),
    3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - RHTower.siegelRadius M ≤ β₁ → β₁ < 1 → 1 < σ → σ ≤ 2 →
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1))

def DHIneqFOf : Prop := DHPos → DHLocal → DHDom → DHIneqF

def DHPrimeOf : Prop := DHHyper → DHPrime

def DHFinish2Of : Prop := DHTuran2 → DHIneqF → DHPrime → DeuringHeilbronnMB

end QH.PrimeProgressions
