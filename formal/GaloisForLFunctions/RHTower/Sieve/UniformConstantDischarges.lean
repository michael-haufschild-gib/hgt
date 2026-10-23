import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegRouteTUniform
import GaloisForLFunctions.RHTower.Sieve.ZetaWideDLVP

/-!
# Uniform constants discharged in `RHTower.Sieve`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/




noncomputable section

namespace RHTower.Sieve

open Complex Metric


/-- `exists_logDeriv_zeta_bound_routeT_of_region` with its constants supplied by
`RHTower.Sieve.exists_routeT_zero_free_region_abs`. -/
theorem exists_logDeriv_zeta_bound_routeT_of_region_uniform :
    ∃ (A : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ σ γ : ℝ, routeTLogDerivThreshold + 1 ≤ |γ| → 1 - routeTZeroFreeWidth A (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 → ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C * Real.log |γ| / routeTZeroFreeWidth A (|γ| + 1) := by
  obtain ⟨A, h_0_0⟩ := RHTower.Sieve.exists_routeT_zero_free_region_abs
  refine ⟨A, ?_⟩
  apply exists_logDeriv_zeta_bound_routeT_of_region <;> assumption

/-- `dlvp_inequality` with its constants supplied by
`RHTower.Sieve.exists_pole_bound`. -/
theorem dlvp_inequality_uniform :
    ∃ (A : ℝ), ∀ (β : ℝ) (γ : ℝ) (δ : ℝ), 3 ≤ |γ| → 0 < δ → δ ≤ 1 / 16 → 1 - β ≤ 1 / 16 → β ≤ 1 → riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
      4 / (1 + δ - β) ≤ 3 / δ + 3 * A + 320 * (5 / 4 * Real.log (7 + 8 * |γ|) + 3 / 4 * Real.log (1 + 1 / δ)) := by
  obtain ⟨A, h_0_0⟩ := RHTower.Sieve.exists_pole_bound
  refine ⟨A, ?_⟩
  intro β γ δ hγ hδ0 hδ hβ hβ1 hzero
  apply dlvp_inequality <;> assumption

/-- `dlvp_inequality_of_bound` with its constants supplied by
`RHTower.Sieve.exists_pole_bound`. -/
theorem dlvp_inequality_of_bound_uniform :
    ∃ (A : ℝ), ∀ (β : ℝ) (γ : ℝ) (δ : ℝ) (R : ℝ) (R₀ : ℝ) (Φ : ℝ), 3 ≤ γ → 0 < δ → δ ≤ 1 / 16 → 0 < R → R < R₀ → R₀ ≤ 1 → (∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R₀, ‖riemannZeta w‖ < Φ) → (∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) R₀, ‖riemannZeta w‖ < Φ) → ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ ≤ Φ → 1 ≤ Φ → β ≤ 1 → 1 + δ - β ≤ R / 2 → riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
      4 / (1 + δ - β) ≤ 3 / δ + 3 * A + 80 / R * (5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6) := by
  obtain ⟨A, h_0_0⟩ := RHTower.Sieve.exists_pole_bound
  refine ⟨A, ?_⟩
  intro β γ δ R R₀ Φ hγ hδ0 hδ hR0 hRR₀ hR₀1 hΦ1 hΦ2 hΦ4 hΦ0 hβ1 hclose hzero
  apply dlvp_inequality_of_bound <;> assumption

end RHTower.Sieve
