import GaloisForLFunctions.RHTower.PhaseAdvanceToSingletonFibre

/-!
# Counting odd fibres from a raw phase increment

The sign-chain interface is stated with an integer anchor `m₀`.  Choosing `m₀ = ⌈ψ(T₁)/π⌉` converts
a raw lower bound `(n+1)π ≤ ψ(T₂) - ψ(T₁)` for the increment into the anchored hypotheses, at the
cost of a single half-turn.
-/

open Set

noncomputable section

namespace RHTower

/-- **`n` odd fibres from an increment of `(n+1)π`.** -/
theorem le_xiOddFiberCount_of_increment {T₁ T₂ : ℝ} (h0 : 0 < T₁) (hT : T₁ ≤ T₂)
    {ρ ψ : ℝ → ℝ} {n : ℕ}
    (hψ : ContinuousOn ψ (Icc T₁ T₂))
    (hρ : ∀ τ ∈ Icc T₁ T₂, 0 < ρ τ)
    (hpolar : ∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ))
    (hadv : ((n : ℝ) + 1) * Real.pi ≤ ψ T₂ - ψ T₁) :
    n ≤ xiOddFiberCount T₂ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set m₀ : ℤ := ⌈ψ T₁ / Real.pi⌉ with hm₀
  have hlow : ψ T₁ ≤ (m₀ : ℝ) * Real.pi := by
    have h := Int.le_ceil (ψ T₁ / Real.pi)
    rw [hm₀]
    rw [div_le_iff₀ hπ] at h
    linarith
  have hhigh : ((m₀ : ℝ) + (n : ℝ)) * Real.pi ≤ ψ T₂ := by
    have h := Int.ceil_lt_add_one (ψ T₁ / Real.pi)
    have h' : (m₀ : ℝ) * Real.pi < ψ T₁ + Real.pi := by
      rw [hm₀]
      have := (mul_lt_mul_of_pos_right h hπ)
      calc (⌈ψ T₁ / Real.pi⌉ : ℝ) * Real.pi
          < (ψ T₁ / Real.pi + 1) * Real.pi := this
        _ = ψ T₁ + Real.pi := by field_simp
    nlinarith [hadv]
  exact le_xiOddFiberCount_of_phase_advance h0 hT hψ hρ hpolar hlow hhigh

/-- The same, delivered as the singleton-fibre bound. -/
theorem xiSingletonFiberCount_ge_of_increment {T₁ T₂ : ℝ} (h0 : 0 < T₁) (hT : T₁ ≤ T₂)
    {ρ ψ : ℝ → ℝ} {n : ℕ}
    (hψ : ContinuousOn ψ (Icc T₁ T₂))
    (hρ : ∀ τ ∈ Icc T₁ T₂, 0 < ρ τ)
    (hpolar : ∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ))
    (hadv : ((n : ℝ) + 1) * Real.pi ≤ ψ T₂ - ψ T₁) :
    (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T₂ : ℝ) / 2
      ≤ (xiSingletonFiberCount T₂ : ℝ) := by
  have h1 := le_xiOddFiberCount_of_increment h0 hT hψ hρ hpolar hadv
  have h2 := three_mul_xiOddFiberCount_le T₂
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T₂ : ℝ) + (xiPosZeroCount T₂ : ℝ) := by
    have : 3 * n ≤ 2 * xiSingletonFiberCount T₂ + xiPosZeroCount T₂ := by omega
    exact_mod_cast this
  linarith

end RHTower

end
