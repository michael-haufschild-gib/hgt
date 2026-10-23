import GaloisForLFunctions.RHTower.VerticalProgressionClassLimits
import GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower.VerticalAP`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower.VerticalAP

open ZetaNotch


/-- `norm_ratioForm_le_crude` with its constants supplied by
`RHTower.VerticalAP.exists_norm_diagHarm_le`. -/
theorem norm_ratioForm_le_crude_uniform :
    ∃ (C₀ : ℝ), ∀ (N : ℕ) (a : ℕ) (b : ℕ), 0 < a → 0 < b → ∀ (t : ℝ), 0 < t →
      ‖ratioForm N a b t‖ ≤ C₀ * (1 + max 0 (Real.log t)) * ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by
  obtain ⟨C₀, h_0_0, h_0_1⟩ := RHTower.VerticalAP.exists_norm_diagHarm_le
  refine ⟨C₀, ?_⟩
  intro N a b ha hb t ht
  apply norm_ratioForm_le_crude <;> assumption

/-- `norm_fiberTerm_crude_le` with its constants supplied by
`RHTower.VerticalAP.exists_norm_diagHarm_le`. -/
theorem norm_fiberTerm_crude_le_uniform :
    ∃ (C₀ : ℝ), ∀ (ψ : ℝ → ℝ), Function.support ψ ⊆ Icc 1 2 → ∀ (Ψ₀ : ℝ), (∀ y, |ψ y| ≤ Ψ₀) → ∀ (α : ℝ) (β : ℝ), 0 < α → ∀ (ε : ℝ), 0 < ε → ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 < T → 2 * |β| ≤ α * T → ∀ (a : ℕ) (b : ℕ), Nat.Coprime a b → 0 < a → 0 < b →
      ‖fiberTerm ψ α β N T (a, b)‖ ≤ (T + 1) * (Ψ₀ * (C₀ * (1 + max 0 (Real.log (3 * α * T))) * (1 + Real.log N) ^ 3 * (Sieve.divisorBoundConst ε * (1 + 1 / ε)) * (((a * b : ℕ) : ℝ) ^ (1 / 2 - 2 * ε))⁻¹)) := by
  obtain ⟨C₀, h_0_0, h_0_1⟩ := RHTower.VerticalAP.exists_norm_diagHarm_le
  refine ⟨C₀, ?_⟩
  intro ψ hsupp Ψ₀ hΨ α β hα ε hε N hN1 T hT0 hβ a b hab ha hb
  apply norm_fiberTerm_crude_le <;> assumption

end RHTower.VerticalAP
