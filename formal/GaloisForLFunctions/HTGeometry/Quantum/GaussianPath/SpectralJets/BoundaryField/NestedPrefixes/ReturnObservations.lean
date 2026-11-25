import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.GateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnClock

/-! # Gate cost on the larger register at actual return dates of a smaller one -/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrescribedTimes SharpOccupation
noncomputable section

/-- A fixed nonnegative integer lag after each smaller-register dip gives
the larger register its ordinary continuous-time gate distribution. All
integer lags, budgets and tolerances share one probability-one event. -/
theorem gaussian_shifted_return_observations :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (k j P s h : ℕ), j<k →
      let x := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
      let t := returnClock (j+1) P s x
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (l : ℕ) (ε : ℝ), ∃ p : ℝ,
        (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H l ε (u T) (u T+T)) atTop (𝓝 p)) ∧
        Tendsto (fun M => (integerClockPrefixLaw (fun i => t i+(h:ℝ)) M : Measure ℝ).real (visitSet H l ε)) atTop (𝓝 p) := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro s
  apply ae_all_iff.mpr
  intro h
  by_cases hj : j<k
  · let x (η : PathPauliDisorder) := fun i => pathPauliDisorderShell η (j+1) (pathCoeffEquiv (j+1) i)
    let t (η : PathPauliDisorder) := returnClock (j+1) P s (x η)
    have hx : Measurable x := (gaussian_pauli_prefix_coordinates_law (j+1)).measurable
    have ht (m : ℕ) : Measurable (fun η => t η m) := (measurable_returnClock _ _ _ m).comp hx
    let u (η : PathPauliDisorder) (m : ℕ) := t η m+(h:ℝ)
    have hu (η : PathPauliDisorder) (m : ℕ) : u η m+1 ≤ u η (m+1) := by
      dsimp only [u]
      rw [add_right_comm]
      exact add_le_add (returnClock_separated (j+1) P s (x η) m) (le_refl (h:ℝ))
    filter_upwards [gaussian_selected_gate_law k u (fun m => (ht m).add_const _) hu] with ω hω
    have he : x (eraseTerminal k ω)=x ω := by dsimp only [x]; rw [shell_before hj]
    have ht' : t (eraseTerminal k ω)=t ω := congrArg (returnClock (j+1) P s) he
    intro _
    dsimp only [u] at hω
    rwa [ht'] at hω
  · exact .of_forall fun _ h => (hj h).elim

/-- Beginning at the actual first post-crossing dip and recording the next
earliest affordable date at least one unit later, the larger register's
gate frequencies are exactly its continuous-time gate frequencies. -/
theorem gaussian_return_observations :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (k j P s : ℕ), j<k →
      let x := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
      let t := returnClock (j+1) P s x
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (l : ℕ) (ε : ℝ), ∃ p : ℝ,
        (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H l ε (u T) (u T+T)) atTop (𝓝 p)) ∧
        Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real (visitSet H l ε)) atTop (𝓝 p) := by
  filter_upwards [gaussian_shifted_return_observations] with ω hω k j P s hj
  simpa only [Nat.cast_zero,add_zero] using hω k j P s 0 hj

#print axioms gaussian_return_observations
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
