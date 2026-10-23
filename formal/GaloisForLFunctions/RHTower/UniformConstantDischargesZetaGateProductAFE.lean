import GaloisForLFunctions.RHTower.ZetaGateDeepLeftLine
import GaloisForLFunctions.RHTower.ZetaGateFarLeftLine
import GaloisForLFunctions.RHTower.ZetaGateRectangleLeftLine

/-!
# Uniform constants discharged in `RHTower.ZetaGateProductAFE`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry MeasureTheory Set Topology

noncomputable section

namespace RHTower.ZetaGateProductAFE

open RHTower


/-- `norm_dualDiagonalIntegrand_rect_le` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightOfOne`, `RHTower.ZetaGateProductAFE.exists_norm_riemannZeta_le_wideLeftStrip`. -/
theorem norm_dualDiagonalIntegrand_rect_le_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → ∀ (v : ℝ),
      ‖dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (v : ℂ) * I)‖ ≤ (8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ) * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightOfOne
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_riemannZeta_le_wideLeftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro d c x τ hd hd20 hc hx v
  apply norm_dualDiagonalIntegrand_rect_le <;> first | assumption | linarith

/-- `norm_dualDiagonalIntegrand_horizontal_rect_le` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_of_two_le_abs`. -/
theorem norm_dualDiagonalIntegrand_horizontal_rect_le_uniform :
    ∃ (CA : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x → ∀ (Cζ : ℝ) (N : ℕ), (∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ N) → 4 ≤ |τ| → ∀ (u : ℝ), -(7 / 10) ≤ u → u ≤ -(1 / 4) → ∀ (ε : ℝ), ε = 1 ∨ ε = -1 →
      ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖ ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ) * (|τ| ^ N * Real.exp (-((|τ| / 2) ^ 2))) := by
  obtain ⟨CA, h_0_0, h_0_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_of_two_le_abs
  refine ⟨CA, ?_⟩
  intro d c x τ hd hd20 hc hx hcx Cζ N hζ hτ u hu1 hu2 ε hε
  apply norm_dualDiagonalIntegrand_horizontal_rect_le <;> first | assumption | linarith

/-- `norm_intervalIntegral_dualDiagonalIntegrand_rect_le` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightOfOne`, `RHTower.ZetaGateProductAFE.exists_norm_riemannZeta_le_wideLeftStrip`. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_rect_le_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 0 ≤ |τ| →
      ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2), dualDiagonalIntegrand d c x τ ((((-(7 / 10) : ℝ) : ℂ)) + (y : ℂ) * I)‖ ≤ (8 * Cχ * Cχ * Cζ * Real.exp (49 / 100)) * (c * x) ^ (7 / 10 : ℝ) * (1 + |τ|) ^ (-(7 / 5 - 2 * d)) * ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightOfOne
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_riemannZeta_le_wideLeftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro d c x τ hd hd20 hc hx hτ
  apply norm_intervalIntegral_dualDiagonalIntegrand_rect_le <;> first | assumption | linarith

/-- `norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_of_two_le_abs`. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le_uniform :
    ∃ (CA : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x → ∀ (Cζ : ℝ) (N : ℕ), 0 ≤ Cζ → (∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ N) → 4 ≤ |τ| → ∀ (ε : ℝ), ε = 1 ∨ ε = -1 →
      ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ), dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖ ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ) * (((N + 2).factorial * Real.exp 2) * (1 + |τ|) ^ (-(2 : ℝ))) * (9 / 20) := by
  obtain ⟨CA, h_0_0, h_0_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_of_two_le_abs
  refine ⟨CA, ?_⟩
  intro d c x τ hd hd20 hc hx hcx Cζ N hCζ hζ hτ ε hε
  apply norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le <;> first | assumption | linarith

/-- `norm_setIntegral_compl_dualDiagonalIntegrand_left_le` with its constants supplied by
`RHTower.exists_norm_zetaChi_le_rightStrip`, `RHTower.exists_norm_riemannZeta_le_leftStrip`. -/
theorem norm_setIntegral_compl_dualDiagonalIntegrand_left_le_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 4 ≤ |τ| →
      ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ, dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖ ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (4 / |τ| ^ 2) * ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(v ^ 2)) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.exists_norm_riemannZeta_le_leftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro d c x τ hd hd20 hc hx hτ
  apply norm_setIntegral_compl_dualDiagonalIntegrand_left_le <;> first | assumption | linarith

/-- `norm_dualDiagonalIntegrand_deep_le` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightStrip_deep`, `RHTower.exists_norm_riemannZeta_le_leftStrip`. -/
theorem norm_dualDiagonalIntegrand_deep_le_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → ∀ (v : ℝ),
      ‖dualDiagonalIntegrand d c x τ ((((-(9 / 20) : ℝ) : ℂ)) + (v : ℂ) * I)‖ ≤ (12 * Cχ * Cχ * Cζ * Real.exp (81 / 400)) * (c * x) ^ (9 / 20 : ℝ) * (1 + |τ|) ^ (-(9 / 10 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.ZetaGateProductAFE.exists_norm_zetaChi_le_rightStrip_deep
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.exists_norm_riemannZeta_le_leftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro d c x τ hd hd20 hc hx v
  apply norm_dualDiagonalIntegrand_deep_le <;> first | assumption | linarith

/-- `norm_setIntegral_compl_dualDiagonalIntegrand_left_le_far` with its constants supplied by
`RHTower.exists_norm_zetaChi_le_rightStrip`, `RHTower.exists_norm_riemannZeta_le_leftStrip`. -/
theorem norm_setIntegral_compl_dualDiagonalIntegrand_left_le_far_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (j : ℕ) (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 4 ≤ |τ| →
      ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ, dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖ ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (2 ^ (4 * j + 2) * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ))) * ∫ v : ℝ, (1 + |v|) ^ (3 + (4 * j + 2)) * Real.exp (-(v ^ 2)) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.exists_norm_riemannZeta_le_leftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro j d c x τ hd hd20 hc hx hτ
  apply norm_setIntegral_compl_dualDiagonalIntegrand_left_le_far <;> first | assumption | linarith

end RHTower.ZetaGateProductAFE
