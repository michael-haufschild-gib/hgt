import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation.ScalarReading
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions

/-! # One fixed-error return record of a smaller register as the observation date -/

open Set Filter MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
open SharpOccupation PrescribedTimes
noncomputable section

/-- At the nth actual smaller-register dip, the probability of a simultaneous
larger-register scalar fit tends to the larger Haar mass. Both budgets on
the smaller register and both errors stay fixed as the record index grows. -/
theorem gaussian_single_return_record {j k : ℕ} (hj : j<k) (P s : ℕ)
    {ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let t (ω : PathPauliDisorder) := returnClock (j+1) P s
      (fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i))
    Tendsto (fun n => pathPauliDisorderLaw.real {ω | orbitCircuitDistance (originalGenerator k ω) 0
      (t ω n)≤ε}) atTop (𝓝 (zeroGateArcDensity (2^(k+3)) (physicalArc ε))) := by
  intro t
  let x (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
  have hx : Measurable x := (gaussian_pauli_prefix_coordinates_law (j+1)).measurable
  have hsame (ω : PathPauliDisorder) : t (eraseTerminal k ω)=t ω := by
    change returnClock (j+1) P s (x (eraseTerminal k ω))=returnClock (j+1) P s (x ω)
    dsimp only [x]
    rw [shell_before hj]
  have hm (n : ℕ) : Measurable (fun ω => t ω n) := (measurable_returnClock _ _ _ n).comp hx
  have hdiv (ω : PathPauliDisorder) : Tendsto (t ω) atTop atTop := by
    have hl (n : ℕ) : t ω 0+(n:ℝ)≤t ω n := by
      induction n with
      | zero => simp only [Nat.cast_zero,add_zero,le_refl]
      | succ n ih =>
        rw [Nat.cast_add_one,←add_assoc]
        exact (add_le_add ih (le_refl 1)).trans (returnClock_separated _ _ _ (x ω) n)
    exact tendsto_atTop_mono hl (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h := scalar_reading k (fun n ω => t ω n) hm (.of_forall fun ω => hdiv (eraseTerminal k ω)) he
  simpa only [hsame] using h

#print axioms gaussian_single_return_record
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.SingleObservation
