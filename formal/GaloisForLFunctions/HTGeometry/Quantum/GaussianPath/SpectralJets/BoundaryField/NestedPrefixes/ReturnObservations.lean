import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.GateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnClock

/-! # Gate cost on the larger register at actual return dates of a smaller one -/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrescribedTimes SharpOccupation
noncomputable section

/-- Almost surely on one chain, read the larger register at the first
low-complexity return after a smaller register's crossing, then at each
subsequent unit-separated low return of that smaller register. The
limiting gate distribution is the ordinary time distribution of the larger
register, simultaneously at all budgets and tolerances. -/
theorem gaussian_return_observations :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (k j P s : ℕ), j<k →
      let x := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
      let t := returnClock (j+1) P s x
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (l : ℕ) (ε : ℝ), ∃ p : ℝ,
        (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H l ε (u T) (u T+T)) atTop (𝓝 p)) ∧
        Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real (visitSet H l ε)) atTop (𝓝 p) := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro s
  by_cases hj : j<k
  · let x (η : PathPauliDisorder) := fun i => pathPauliDisorderShell η (j+1) (pathCoeffEquiv (j+1) i)
    let t (η : PathPauliDisorder) := returnClock (j+1) P s (x η)
    have hx : Measurable x := (gaussian_pauli_prefix_coordinates_law (j+1)).measurable
    have ht (m : ℕ) : Measurable (fun η => t η m) := (measurable_returnClock _ _ _ m).comp hx
    filter_upwards [gaussian_selected_gate_law k t ht (fun η => returnClock_separated _ _ _ (x η))] with ω hω
    have he : x (eraseTerminal k ω)=x ω := by dsimp only [x]; rw [shell_before hj]
    have ht' : t (eraseTerminal k ω)=t ω := congrArg (returnClock (j+1) P s) he
    intro _
    rwa [ht'] at hω
  · exact .of_forall fun _ h => (hj h).elim

#print axioms gaussian_return_observations
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
