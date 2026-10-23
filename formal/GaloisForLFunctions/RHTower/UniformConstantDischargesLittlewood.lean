import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount

/-!
# Uniform constants discharged in `RHTower.Littlewood`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.Littlewood

open Complex Filter MeasureTheory Set Topology Zeta23

/-- `mu_add_le` with its constants supplied by
`RHTower.Littlewood.exists_stirling`. -/
theorem mu_add_le_uniform :
    ∃ (C : ℝ), ∀ (T : ℝ), 1 ≤ T → ∀ (x : ℝ),
      mu (x + T) ≤ mu (3 * T / 2) + (1 / (2 * Real.pi) + C) * (4 / T ^ 2 * x ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.Littlewood.exists_stirling
  refine ⟨C, ?_⟩
  intro T hT x
  apply mu_add_le <;> assumption

/-- `mu_half_le` with its constants supplied by
`RHTower.Littlewood.exists_stirling`. -/
theorem mu_half_le_uniform :
    ∃ (C : ℝ), ∀ (T : ℝ), 2 ≤ T →
      mu (T / 2) ≤ T + C := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.Littlewood.exists_stirling
  refine ⟨C, ?_⟩
  intro T hT
  apply mu_half_le <;> assumption

/-- `mu_half_sub_ge` with its constants supplied by
`RHTower.Littlewood.exists_stirling`. -/
theorem mu_half_sub_ge_uniform :
    ∃ (C : ℝ), ∀ (T : ℝ), 2 ≤ T →
      (Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) - 2 * C ≤ mu (T / 2) - mu (3 * T / 2) / 2 := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.Littlewood.exists_stirling
  refine ⟨C, ?_⟩
  intro T hT
  apply mu_half_sub_ge <;> assumption

end RHTower.Littlewood
