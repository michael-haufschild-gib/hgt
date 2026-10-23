import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianResidueGrowth

/-!
# Uniform constants discharged in `RHTower.DeningerMeyerGaussianGreen`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.DeningerMeyerGaussianGreen

open Complex Filter Set Topology
open scoped Real

/-- `pi_le_norm_Gamma_half_mul` with its constants supplied by
`RHTower.DeningerMeyerGaussianGreen.exists_gamma_bound_Icc`. -/
theorem pi_le_norm_Gamma_half_mul_uniform :
    ∃ (M : ℝ), ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      Real.pi ≤ ‖Complex.Gamma (ρ / 2)‖ * M * Real.exp (Real.pi * |ρ.im| / 2) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.DeningerMeyerGaussianGreen.exists_gamma_bound_Icc
  refine ⟨M, ?_⟩
  intro ρ h0 h1
  apply pi_le_norm_Gamma_half_mul <;> assumption

/-- `norm_archFactor_lower` with its constants supplied by
`RHTower.DeningerMeyerGaussianGreen.exists_gamma_bound_Icc`. -/
theorem norm_archFactor_lower_uniform :
    ∃ (M : ℝ), ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      ρ.im ^ 2 / (2 * M * Real.exp (Real.pi * |ρ.im| / 2)) ≤ ‖archFactor ρ‖ := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.DeningerMeyerGaussianGreen.exists_gamma_bound_Icc
  refine ⟨M, ?_⟩
  intro ρ h0 h1
  apply norm_archFactor_lower <;> assumption

end RHTower.DeningerMeyerGaussianGreen
