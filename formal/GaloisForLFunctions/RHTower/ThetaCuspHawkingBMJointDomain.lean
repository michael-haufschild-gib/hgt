import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointDifferentialGraph
import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator

/-! Faithfulness and the self-adjoint operator of the completed actual joint differential domain. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointWave
noncomputable section

private theorem jointEmbedding_zero (u : jointDomain) (hu : jointEmbedding u = 0) : u = 0 := by
  have hr : (u : JointEnergySpace) 1 = 0 := by
    apply spatialValue_total
    intro f g
    have h := radialConstraint_completed f g u
    change inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.fieldVector g))
        ((u : JointEnergySpace) 1) +
      inner ℂ (l2SeparatedProduct (radialDerivative f) (D4BMModularCore.fieldVector g))
        (jointEmbedding u) = 0 at h
    simpa only [hu,inner_zero_right,add_zero] using h
  have ha (i : Fin 2) : (u : JointEnergySpace) i.succ.succ = 0 := by
    apply spatialMass_total
    intro f g
    have h := angularConstraint_completed f g i u
    change inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.massTest g))
        ((u : JointEnergySpace) i.succ.succ) +
      inner ℂ (l2SeparatedProduct (radialWeightedValue f)
        (D4BMModularCore.fluxTest g (D4BMModularCore.direction i))) (jointEmbedding u) = 0 at h
    simpa only [hu,inner_zero_right,add_zero] using h
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hu
  · exact hr
  · exact ha 0
  · exact ha 1

/-- No completed derivative can survive over a zero scalar field: the actual joint graph is closable. -/
theorem jointEmbedding_injective : Function.Injective jointEmbedding := by
  intro u v huv
  have hz : jointEmbedding (u-v) = 0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (jointEmbedding_zero _ hz)

/-- The exact completed form retains radial energy and both weighted angular energies. -/
theorem joint_inner_decomposition (u v : jointDomain) :
    inner ℂ u v = inner ℂ (jointEmbedding u) (jointEmbedding v) +
      ∑ i : Fin 3, inner ℂ ((u : JointEnergySpace) i.succ) ((v : JointEnergySpace) i.succ) := by
  change inner ℂ (u : JointEnergySpace) (v : JointEnergySpace) = _
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  rfl

/-- The source-independent joint Friedrichs operator, with the scalar mass term included. -/
def jointEnergyOperator : SpatialSpace →ₗ.[ℂ] SpatialSpace :=
  friedrichsFormOperator jointEmbedding

theorem jointEnergyOperator_selfAdjoint : IsSelfAdjoint jointEnergyOperator :=
  friedrichsFormOperator_isSelfAdjoint jointEmbedding jointEmbedding_injective jointEmbedding_dense

theorem jointEnergyOperator_closed : jointEnergyOperator.IsClosed :=
  friedrichsFormOperator_isClosed jointEmbedding jointEmbedding_injective jointEmbedding_dense

theorem jointEnergyOperator_denseDomain : Dense (jointEnergyOperator.domain : Set SpatialSpace) :=
  friedrichsFormOperator_dense_domain jointEmbedding jointEmbedding_injective jointEmbedding_dense

end
end RHTower.D4BMJointWave
