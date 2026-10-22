import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricPencil
import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# Closed-graph barrier for the singular theta metric

The source-faithful theta metric is injective, but it has no positive lower bound.  Consequently
its range is not closed.  A closed relation realizing the metric pencil therefore cannot obtain
its domain topology from the metric coordinate alone: it needs a genuinely new closed-graph
coordinate.  This isolates the exact missing ingredient in the index-one dilation route.
-/

open scoped Topology InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- The singular theta metric cannot by itself serve as a closed graph coordinate. -/
theorem not_isClosed_range_thetaMetricOperator :
    ¬ IsClosed (Set.range thetaMetricOperator) := by
  intro hclosed
  obtain ⟨c, hc, hbound⟩ :=
    (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range thetaMetricOperator).mpr hclosed
  apply not_boundedBelow_thetaMetricOperator
  refine ⟨c, hc, ?_⟩
  intro f
  apply hbound f
  rw [LinearMap.ker_eq_bot.mpr thetaMetricOperator_injective]
  simp

end

end RHTower
