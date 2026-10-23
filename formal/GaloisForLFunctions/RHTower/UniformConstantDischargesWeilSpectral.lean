import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest

/-!
# Uniform constants discharged in `RHTower.WeilSpectral`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.WeilSpectral

open Complex Filter MeasureTheory Set Topology Zeta23
open scoped ComplexConjugate ENNReal NNReal Real

/-- `abs_truncTestDeriv_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem abs_truncTestDeriv_le_uniform :
    ∃ (Λ : ℝ), ∀ (F : ℝ → ℝ) (L : ℝ) (u : ℝ),
      |truncTestDeriv F L u| ≤ |deriv F u| + 2 * Λ * |F u| := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro F L u
  apply abs_truncTestDeriv_le <;> assumption

/-- `weighted_truncTest_sub_le_indicator` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem weighted_truncTest_sub_le_indicator_uniform :
    ∃ (Λ : ℝ), ∀ (F : ℝ → ℝ) (L : ℝ) (M : ℝ), L ≤ M → ∀ (u : ℝ),
      ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) + ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ≤ {u : ℝ | L - 1 ≤ |u|}.indicator (tailMajorant F Λ) u := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro F L M hLM u
  apply weighted_truncTest_sub_le_indicator <;> assumption

end RHTower.WeilSpectral
