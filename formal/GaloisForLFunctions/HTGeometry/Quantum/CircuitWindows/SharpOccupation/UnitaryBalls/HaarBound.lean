import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.GlobalPhase.PhaseCubes

/-! # Sharp Haar bound for a phase packet near an arbitrary unitary -/
open Matrix Set MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An operator ball at tolerance ε excludes an antipodal eigenvector
throughout a surrounding phase cube when the opposite chord exceeds ε. -/
theorem volume_fixed_target_chord {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    {ε g : ℝ} (hg : 0≤g) (hg' : g<1) (he : ε<2*Real.cos (Real.pi*g/2)) :
    volume {x : UnitAddTorus I | ‖C-packet x‖≤ε} ≤ ENNReal.ofReal (1-g)^Fintype.card I := by
  simpa only [phaseCube_zero,zero_add] using
    volume_phaseCube_chord hC (r:=0) le_rfl hg (by simpa only [zero_add] using hg') (by simpa only [zero_add] using he)

/-- For every operator error below two, any fixed unitary captures at
most xᴰ of independent phases, where the allowed angular width is x turns. -/
theorem volume_fixed_unitary_ball {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    {x : ℝ} (hx : x∈Ico (0:ℝ) 1) :
    volume {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x} ≤ ENNReal.ofReal x^Fintype.card I := by
  simpa only [phaseCube_zero,add_zero] using
    volume_phaseCube_ball hC hx.1 (r:=0) le_rfl (by simpa only [add_zero] using hx.2)

#print axioms volume_fixed_unitary_ball
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
