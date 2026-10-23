import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity
import GaloisForLFunctions.RHTower.XiLaguerreShadowScaledDensity

/-!
# Uniform constants discharged in `RHTower.DeBruijn`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.DeBruijn

open Complex Filter MeasureTheory Set Topology

/-- `eventually_volume_xiShadowScaled_inter_Icc_le_of_moment` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul`. -/
theorem eventually_volume_xiShadowScaled_inter_Icc_le_of_moment_uniform :
    ∃ (μ : ℝ), ∀ (κ : ℝ), 0 ≤ κ →
      ∀ᶠ V in atTop, volume (xiShadowScaled κ ∩ Icc 0 V) ≤ ENNReal.ofReal (2 * κ * μ * V + κ ^ 2 * μ) := by
  obtain ⟨μ, h_0_0⟩ := RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul
  refine ⟨μ, ?_⟩
  intro κ hκ
  apply eventually_volume_xiShadowScaled_inter_Icc_le_of_moment <;> assumption

/-- `eventually_volume_xiShadow_inter_Icc_le_of_moment` with its constants supplied by
`RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul`. -/
theorem eventually_volume_xiShadow_inter_Icc_le_of_moment_uniform :
    ∃ (μ : ℝ), ∀ᶠ V in atTop, volume (xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal (2 * μ * V + μ) := by
  obtain ⟨μ, h_0_0⟩ := RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul
  refine ⟨μ, ?_⟩
  apply eventually_volume_xiShadow_inter_Icc_le_of_moment <;> assumption

end RHTower.DeBruijn
