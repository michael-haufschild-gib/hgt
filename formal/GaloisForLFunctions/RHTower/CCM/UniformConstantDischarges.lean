import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaFarTail
import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaLayerBounds

/-!
# Uniform constants discharged in `RHTower`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower

open Complex Filter MeasureTheory RHTower.CCMFullGroundEigen RHTower.CCMRealRootedGround Real Set Topology Zeta23
open scoped ComplexConjugate Real

/-- `abs_deriv_bartaCutoff_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem abs_deriv_bartaCutoff_le_uniform :
    ∃ (Λ : ℝ), ∀ (c : ℝ) (w : ℝ), 0 < w → ∀ (t : ℝ),
      |deriv (bartaCutoff c w) t| ≤ 2 * Λ / w := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro c w hw t
  apply abs_deriv_bartaCutoff_le <;> assumption

/-- `norm_bartaFarDefect_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_bartaFarDefect_le_uniform :
    ∃ (Λ : ℝ), ∀ (c : ℝ) (Λ₂ : ℝ), 1 < c → (∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ Λ₂) → ∀ (t : ℝ),
      ‖bartaFarDefect c t‖ ≤ 2 * ‖riemannKernelDeriv 2 t‖ + 4 * Λ * ‖riemannKernelDeriv 1 t‖ + Λ₂ * ‖riemannKernelDeriv 0 t‖ := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro c Λ₂ hc hΛ₂ t
  apply norm_bartaFarDefect_le <;> assumption

/-- `norm_bartaFarDefect_mul_exp_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_bartaFarDefect_mul_exp_le_uniform :
    ∃ (Λ : ℝ), ∀ (b : ℝ) (Λ₂ : ℝ), 1 ≤ b → (∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ Λ₂) → ∀ (u : ℝ),
      ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤ (2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) + Λ₂ * cuspDecayConst (riemannKernelPoly 0)) * (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1))) * Real.exp (-|u|) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro b Λ₂ hb hΛ₂ u
  apply norm_bartaFarDefect_mul_exp_le <;> assumption

end RHTower
