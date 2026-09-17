import GaloisForLFunctions.HTGeometry.HorizonPowerThirdJointContinuityCore
import GaloisForLFunctions.HTGeometry.CompactContinuousNormBound

/-! Uniform compact-family bound for the literal third source-power derivative. -/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology Metric
noncomputable section
set_option autoImplicit false

/-- On the fixed physical half-cutoff, one finite constant bounds the literal
third source-power derivative throughout every unit closed frequency ball. -/
theorem exists_horizonPowerThirdCore_uniform_bound (α₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ closedBall α₀ 1, ∀ z ∈ Icc (0 : ℝ) (1 / 2),
      ‖horizonPowerThirdCore α z‖ ≤ C := by
  let K : Set (ℂ × ℝ) := closedBall α₀ 1 ×ˢ Icc (0 : ℝ) (1 / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hcont : ContinuousOn (fun q : ℂ × ℝ => horizonPowerThirdCore q.1 q.2) K := by
    intro q hq
    have hq1 : q.2 < 1 := by linarith [hq.2.2]
    exact (horizonPowerThirdCore_joint_continuousAt q hq1).continuousWithinAt
  obtain ⟨C, hC0, hC⟩ := exists_compact_continuous_norm_bound hK _ hcont
  refine ⟨C, hC0, ?_⟩
  intro α hα z hz
  exact hC (α, z) ⟨hα, hz⟩

end
end GaloisForLFunctions.HTGeometry
