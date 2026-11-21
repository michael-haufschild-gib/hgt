import Mathlib

/-! The primitive explicit formula with zero multiplicities and a finite height cutoff. -/

noncomputable section

namespace PI

open Classical in

def psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
    (if χ = 1 then (u : ℂ) else 0)

theorem measurable_psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) : Measurable (psi0 χ) := by
  unfold psi0
  apply Measurable.sub
  · exact (measurable_from_nat (f := fun m : ℕ => ∑ n ∈ Finset.Icc 1 m,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N))).comp Nat.measurable_floor
  · by_cases h : χ = 1
    · simp only [if_pos h]
      exact Complex.measurable_ofReal
    · simp only [if_neg h]
      exact measurable_const

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ExplicitFormulaWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)

def ExplicitFormula : Prop := ∃ C : ℝ, 0 < C ∧ ExplicitFormulaWith C

end PI
