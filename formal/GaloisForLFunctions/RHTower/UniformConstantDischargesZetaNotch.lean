import GaloisForLFunctions.RHTower.ZetaSquareDiagonalHarmonic

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower.ZetaNotch`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower.ZetaNotch



/-- `norm_diagHarmIntegrand_le` with its constants supplied by
`RHTower.ZetaNotch.exists_bound_norm_riemannZeta₁_strip`. -/
theorem norm_diagHarmIntegrand_le_uniform :
    ∃ (C : ℝ) (N : ℕ), ∀ (x : ℝ), 0 < x → ∀ (u : ℝ) (v : ℝ), -1 / 4 ≤ u → u ≤ 1 → (u : ℂ) + (v : ℂ) * I ≠ 0 →
      ‖diagHarmIntegrand x ((u : ℂ) + (v : ℂ) * I)‖ ≤ x ^ u * Real.exp (u ^ 2 - v ^ 2) * (C * (1 + 2 * |v|) ^ N) / (2 * ‖(u : ℂ) + (v : ℂ) * I‖ ^ 2) := by
  obtain ⟨C, N, h_0_0, h_0_1⟩ := RHTower.ZetaNotch.exists_bound_norm_riemannZeta₁_strip
  refine ⟨C, N, ?_⟩
  intro x hx u v hu1 hu2 hw
  apply norm_diagHarmIntegrand_le <;> assumption

end RHTower.ZetaNotch
