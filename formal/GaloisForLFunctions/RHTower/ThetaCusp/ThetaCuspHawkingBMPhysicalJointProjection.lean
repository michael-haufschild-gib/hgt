import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMWeightedJointSource
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularProjectionMeromorphy

/-! A bounded physical testing map for the complete original source, with exact integral identification. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Radial extension of the physical source functional on height-weighted joint representatives.
This is the adjoint of tensor insertion; it does not assert an outgoing resolvent identity. -/
def physicalJointProjection (q : XiZeroCopy) : SpatialSpace →L[ℂ] Lp ℂ 2 radialMeasure :=
  (l2SeparatedProductContinuousBilinear.flip (physicalDualVector q) :
    Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace).adjoint

/-- Exact physical contraction on every separated source, without a radial domain restriction. -/
theorem physicalJointProjection_separated (q : XiZeroCopy)
    (f : Lp ℂ 2 radialMeasure) (g : D4BMModularCore.Space) :
    physicalJointProjection q (l2SeparatedProductContinuousBilinear f g) =
      physicalAngularFunctional q g • f := by
  apply ext_inner_left ℂ
  intro h
  unfold physicalJointProjection
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (l2SeparatedProduct h (physicalDualVector q)) (l2SeparatedProduct f g) = _
  rw [l2SeparatedProduct_inner,inner_smul_right]
  change inner ℂ h f * inner ℂ (physicalDualVector q) g =
    inner ℂ (physicalDualVector q) g * inner ℂ h f
  exact mul_comm _ _

/-- The weighted Hilbert projection equals the original physical angular integral of the
complete source, including all three differential cutoff channels and arbitrary Xi targets. -/
theorem physicalJointProjection_complete_source (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalJointProjection r (weightedCuspResidualL2 q branch a w) =
      continuedAngularSourceL2 q branch (physicalAngularParameter r) a w := by
  rw [weightedCuspResidualL2_assembly q branch w a hw hwr,
    continuedAngularSourceL2_assembly q branch (physicalAngularParameter r) a w hw hwr,
    map_add,map_sum]
  simp only [physicalJointProjection_separated,physicalAngularFunctional_native,
    physicalAngularFunctional_cutoff,scalarCutoffPeriod_eq_boundary_value]

end
end RHTower.D4BMJointSource
