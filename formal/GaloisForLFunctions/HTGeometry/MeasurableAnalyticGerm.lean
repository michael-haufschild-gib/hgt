import GaloisForLFunctions.Bottcher.InverseBranchPeriodic
import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every analytic germ has a globally measurable representative agreeing on a neighborhood. -/
theorem exists_measurable_eventuallyEq_of_analyticAt
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ g : ℂ → ℂ, Measurable g ∧ AnalyticAt ℂ g a ∧ f =ᶠ[nhds a] g := by
  let K : NNReal := ⟨‖deriv f a‖ + 1, by positivity⟩
  have hK : ‖deriv f a‖ < (K : ℝ) := by
    change ‖deriv f a‖ < ‖deriv f a‖ + 1
    linarith
  obtain ⟨r, hr, hball⟩ :=
    Bottcher.exists_closedBall_deriv_bound_of_analyticAt hf hK
  have hlip : LipschitzOnWith K f (closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro z hz
      exact (hball z hz).1.hasDerivWithinAt
    · intro z hz
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hball z hz).2
  obtain ⟨g, hgLip, hfg⟩ :=
    GaloisForLFunctions.LipschitzOnWith.extend_complex hlip
  have hev : f =ᶠ[nhds a] g := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact hfg (mem_closedBall.mpr (mem_ball.mp hz).le)
  refine ⟨g, hgLip.continuous.measurable, ?_, hev⟩
  exact hf.congr hev

end

end GaloisForLFunctions.HTGeometry
