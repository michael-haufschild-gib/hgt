import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaFarTail
import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaLayerBounds
import GaloisForLFunctions.RHTower.RiemannKernelTruncationWeilPositive

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter MeasureTheory Real Set Topology Zeta23
open scoped ComplexConjugate Real

noncomputable section

namespace RHTower

open RHTower.CCMFullGroundEigen RHTower.CCMRealRootedGround


/-- `abs_deriv_bartaCutoff_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem abs_deriv_bartaCutoff_le_uniform :
    ∃ (Λ : ℝ), ∀ (c : ℝ) (w : ℝ), 0 < w → ∀ (t : ℝ),
      |deriv (bartaCutoff c w) t| ≤ 2 * Λ / w := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro c w hw t
  apply abs_deriv_bartaCutoff_le <;> assumption

/-- Uniform bound on the second derivative of the smooth transition, as an iterated derivative. -/
theorem exists_abs_iteratedDeriv_two_smoothTransition_le :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ S := by
  obtain ⟨S, hS, h⟩ := exists_abs_deriv_deriv_smoothTransition_le
  refine ⟨S, hS, fun x => ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact h x

/-- `norm_bartaFarDefect_le` with the two smooth-transition derivative bounds supplied. -/
theorem norm_bartaFarDefect_le_uniform :
    ∃ Λ Λ₂ : ℝ, 0 ≤ Λ ∧ 0 ≤ Λ₂ ∧ ∀ c : ℝ, 1 < c → ∀ t : ℝ,
      ‖bartaFarDefect c t‖ ≤ 2 * ‖riemannKernelDeriv 2 t‖ + 4 * Λ * ‖riemannKernelDeriv 1 t‖ +
        Λ₂ * ‖riemannKernelDeriv 0 t‖ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨Λ₂, hΛ₂0, hΛ₂⟩ := exists_abs_iteratedDeriv_two_smoothTransition_le
  exact ⟨Λ, Λ₂, hΛ0, hΛ₂0, fun c hc t => norm_bartaFarDefect_le hc hΛ hΛ₂ t⟩

/-- `norm_bartaFarDefect_mul_exp_le` with the two smooth-transition derivative bounds supplied. -/
theorem norm_bartaFarDefect_mul_exp_le_uniform :
    ∃ Λ Λ₂ : ℝ, 0 ≤ Λ ∧ 0 ≤ Λ₂ ∧ ∀ b : ℝ, 1 ≤ b → ∀ u : ℝ,
      ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤
        (2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) +
          Λ₂ * cuspDecayConst (riemannKernelPoly 0)) *
          (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1))) * Real.exp (-|u|) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨Λ₂, hΛ₂0, hΛ₂⟩ := exists_abs_iteratedDeriv_two_smoothTransition_le
  exact ⟨Λ, Λ₂, hΛ0, hΛ₂0, fun b hb u => norm_bartaFarDefect_mul_exp_le hb hΛ hΛ₂ u⟩

end RHTower
