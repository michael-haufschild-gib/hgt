import GaloisForLFunctions.RHTower.KFreeAbelSmoothedSaving

/-!
# Uniform constants discharged in `RHTower.KFreeAbel`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.KFreeAbel

open Complex Filter MeasureTheory Topology

/-- `norm_kFree_horizontal_edge_le` with its constants supplied by
`RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re`. -/
theorem norm_kFree_horizontal_edge_le_uniform :
    ∃ (Bz : ℝ), ∀ (k : ℕ), 2 ≤ k → ∀ (t : ℝ) (a : ℝ) (c : ℝ) (K : ℝ) (A : ℝ) (V : ℝ) (y : ℝ), 0 < t → t < 1 → a ≤ c → 0 ≤ c → c ≤ 2 → 1 ≤ K → 0 ≤ A → 0 ≤ V → |y| = K → (∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) → ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ≤ A * Real.exp (-(|y| / 4))) → (∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w.re ≤ 2 → ‖Sieve.invZeta w‖ ≤ V) →
      ‖∫ σ in c..2, kFreeAbelIntegrand k t ((σ : ℂ) + (y : ℂ) * I)‖ ≤ t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) * 2 := by
  obtain ⟨Bz, h_0_0, h_0_1⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨Bz, ?_⟩
  intro k hk t a c K A V y ht ht1 hca hc0 hc2 hK1 hA hV hy hΓζ hinvV
  apply norm_kFree_horizontal_edge_le <;> assumption

/-- `norm_kFree_line_le` with its constants supplied by
`RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re`. -/
theorem norm_kFree_line_le_uniform :
    ∃ (Bz : ℝ), ∀ (k : ℕ), 2 ≤ k → ∀ (t : ℝ) (a : ℝ) (A : ℝ), 0 < t → a ≤ 2 → (∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) → ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ≤ A * Real.exp (-(|y| / 4))) → ∀ (y : ℝ),
      ‖kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * |y|)) := by
  obtain ⟨Bz, h_0_0, h_0_1⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨Bz, ?_⟩
  intro k hk t a A ht ha2 hΓζ y
  apply norm_kFree_line_le <;> assumption

/-- `norm_integral_kFree_sub_residue_le` with its constants supplied by
`RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re`. -/
theorem norm_integral_kFree_sub_residue_le_uniform :
    ∃ (Bz : ℝ), ∀ (k : ℕ), 2 ≤ k → ∀ (t : ℝ) (a : ℝ) (c : ℝ) (K : ℝ) (A : ℝ) (V : ℝ), 0 < t → t < 1 → 0 < a → a ≤ c → c ≤ 3 / 4 → k * c ≤ 2 → 1 ≤ K → 0 ≤ A → 0 ≤ V → (∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) → ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ≤ A * Real.exp (-(|y| / 4))) → (∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w.re ≤ 2 → ‖Sieve.invZeta w‖ ≤ V) → (∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w ≠ 1 → riemannZeta w ≠ 0) →
      ‖(∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)) - 2 * Real.pi * kFreeAbelPoleFactor k t 1‖ ≤ t ^ (-c) * A * V * (2 * K) + 2 * (t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) * 2) + t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * K / 2)) * ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|)) := by
  obtain ⟨Bz, h_0_0, h_0_1⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨Bz, ?_⟩
  intro k hk t a c K A V ht ht1 ha hca hc34 hkc hK1 hA hV hΓζ hinvV hzf
  apply norm_integral_kFree_sub_residue_le <;> assumption

end RHTower.KFreeAbel
