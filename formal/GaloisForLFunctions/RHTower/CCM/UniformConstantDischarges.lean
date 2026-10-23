import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaFarTail
import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaLayerBounds

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



end RHTower
