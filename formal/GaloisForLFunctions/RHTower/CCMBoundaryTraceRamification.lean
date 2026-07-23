import GaloisForLFunctions.HTGeometry.BoundaryTraceRamification
import GaloisForLFunctions.RHTower.CCMCommensurateJointShiftSpectrumRigidity

/-!
# CCM four-unit boundary ramification

This file applies the universal thermal boundary law to the exact four-unit
normalization singled out by the CCM source geometry.  Any Hilbert, Hilbert--
Schmidt, or other normed-space curve carrying that normalization has a forced
square-root boundary scale and cannot extend differentiably through `u = 0`.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E]

/-- Exact four-unit CCM normalization forces square-root-normalized amplitude
two.  The statement is independent of dimension, rank, and operator model. -/
theorem ccmFourUnitBoundaryCurve_squareRootLaw
    {F : ℝ → E}
    (hfour : Tendsto (HTGeometry.thermalBoundaryTraceDensity F) (𝓝[>] 0) (nhds 4)) :
    Tendsto (HTGeometry.thermalBoundaryRamificationAmplitude F) (𝓝[>] 0) (nhds 2) := by
  convert HTGeometry.tendsto_thermalBoundaryRamificationAmplitude hfour using 1
  norm_num

section Differentiable

variable [NormedSpace ℝ E]

/-- No norm-differentiable boundary curve can realize the positive four-unit
CCM density while vanishing at the source boundary. -/
theorem ccmFourUnitBoundaryCurve_not_hasDerivAt
    {F : ℝ → E} (hF0 : F 0 = 0)
    (hfour : Tendsto (HTGeometry.thermalBoundaryTraceDensity F) (𝓝[>] 0) (nhds 4)) :
    ¬ ∃ v : E, HasDerivAt F v 0 := by
  exact HTGeometry.not_hasDerivAt_of_thermalBoundaryTraceDensity_tendsto_pos
    hF0 (by norm_num) hfour

end Differentiable

end RHTower
