import GaloisForLFunctions.RHTower.MoebiusAbelSmoothedSaving

/-!
# Uniform constants discharged in `RHTower.MoebiusAbel`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.MoebiusAbel

open Complex Filter MeasureTheory Topology

/-- `abelMoebiusIntegrand_line_le` with its constants supplied by
`RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re`. -/
theorem abelMoebiusIntegrand_line_le_uniform :
    ∃ (Bz : ℝ), ∀ (x : ℝ), 0 < x → ∀ (A : ℝ), (∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2))) → ∀ (t : ℝ),
      ‖abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(|t| / 2)) := by
  obtain ⟨Bz, h_0_0, h_0_1⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨Bz, ?_⟩
  intro x hx A hΓ t
  apply abelMoebiusIntegrand_line_le <;> assumption

/-- `norm_left_edge_le` with its constants supplied by
`RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half`. -/
theorem norm_left_edge_le_uniform :
    ∃ (A : ℝ), ∀ (x : ℝ) (c : ℝ) (K : ℝ) (V : ℝ), 0 < x → 1 / 2 ≤ c → c ≤ 2 → 0 ≤ K → (∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V) →
      ‖∫ y in (-K)..K, abelMoebiusIntegrand x ((c : ℂ) + (y : ℂ) * I)‖ ≤ x ^ (-c) * A * V * (2 * K) := by
  obtain ⟨A, h_0_0, h_0_1⟩ := RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half
  refine ⟨A, ?_⟩
  intro x c K V hx hc12 hc2 hK0 hinvR
  apply norm_left_edge_le <;> assumption

/-- `norm_horizontal_edge_le` with its constants supplied by
`RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half`. -/
theorem norm_horizontal_edge_le_uniform :
    ∃ (A : ℝ), ∀ (x : ℝ) (c : ℝ) (K : ℝ) (V : ℝ) (y : ℝ), 0 < x → x < 1 → 1 / 2 ≤ c → c ≤ 2 → 0 ≤ V → |y| = K → (∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V) →
      ‖∫ σ in c..2, abelMoebiusIntegrand x ((σ : ℂ) + (y : ℂ) * I)‖ ≤ x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V * 2 := by
  obtain ⟨A, h_0_0, h_0_1⟩ := RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half
  refine ⟨A, ?_⟩
  intro x c K V y hx hx1 hc12 hc2 hV hy hinvR
  apply norm_horizontal_edge_le <;> assumption

/-- `norm_integral_abelMoebiusIntegrand_le` with its constants supplied by
`RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half`, `RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re`. -/
theorem norm_integral_abelMoebiusIntegrand_le_uniform :
    ∃ (A : ℝ) (Bz : ℝ), ∀ (x : ℝ) (K : ℝ) (c : ℝ) (V : ℝ), 0 < x → x < 1 → 0 ≤ K → 1 / 2 ≤ c → c ≤ 2 → 0 ≤ V → (∀ s : ℂ, |s.im| ≤ K → c ≤ s.re → s.re ≤ 2 → ‖Sieve.invZeta s‖ ≤ V) → (∀ s ∈ Set.uIcc c 2 ×ℂ Set.uIcc (-K) K, s ≠ 1 → riemannZeta s ≠ 0) →
      ‖∫ t : ℝ, abelMoebiusIntegrand x (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ x ^ (-c) * A * V * (2 * K) + 2 * (x ^ (-(2 : ℝ)) * A * Real.exp (-(K / 2)) * V * 2) + x ^ (-(2 : ℝ)) * A * Bz * Real.exp (-(K / 4)) * ∫ t : ℝ, Real.exp (-((1 / 4 : ℝ) * |t|)) := by
  obtain ⟨A, h_0_0, h_0_1⟩ := RHTower.MoebiusAbel.exists_norm_Gamma_le_exp_half
  obtain ⟨Bz, h_1_0, h_1_1⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨A, Bz, ?_⟩
  intro x K c V hx hx1 hK0 hc12 hc2 hV hinvR hzfR
  apply norm_integral_abelMoebiusIntegrand_le <;> assumption

end RHTower.MoebiusAbel
