import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.GlobalPhase.Rotation

/-! # Projective Haar capture by an arbitrary fixed unitary -/
open Set Matrix MeasureTheory Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Scalar phase optimization costs at most the reciprocal angular
slack, at every operator tolerance short of a full turn. -/
theorem volume_projective_unitary_ball {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    {x r : ℝ} (hx : 0≤x) (hr : 0≤r) (hxr : x+r<1) :
    ENNReal.ofReal r*volume (rotations {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x}) ≤
      ENNReal.ofReal (x+r)^Fintype.card I := by
  have hc : IsClosed {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x} :=
    isClosed_le (continuous_const.sub packet_continuous).norm continuous_const
  exact (rotation_volume hc ⟨r,hr,by linarith only [hx,hxr]⟩).trans (volume_phaseCube_ball hC hx hr hxr)

#print axioms volume_projective_unitary_ball
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
