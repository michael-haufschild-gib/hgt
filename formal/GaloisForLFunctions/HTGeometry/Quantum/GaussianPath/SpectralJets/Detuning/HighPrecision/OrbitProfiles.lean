import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.ScalarWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ScalarDistance

/-! # Repetition of the full circuit-distance profile in a bounded horizon -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
open SharpOccupation (Register)
noncomputable section

/-- Every phase of the circuit-complexity trajectory repeats in each
doubly exponential observation window. One time translation achieves
inverse-exponential operator error simultaneously at all budgets and
all past and future offsets. -/
theorem gaussian_uniform_profile_recurrence :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ a v : ℝ, ∃ z ∈ Icc a (a+(2:ℝ)^(D^C)), ∀ t : ℝ, ∀ s : ℕ,
        |orbitCircuitDistance H s (z+t)-orbitCircuitDistance H s (v+t)| ≤ 1/(2:ℝ)^D := by
  obtain ⟨C,hC⟩ := gaussian_fine_scalar_windows
  refine ⟨C,?_⟩
  filter_upwards [hC] with ω hω
  filter_upwards [hω] with k hk
  intro N D u H a v
  obtain ⟨w,hw,hfit⟩ := hk (a-v)
  refine ⟨v+w,⟨by linarith only [hw.1],by linarith only [hw.2]⟩,?_⟩
  intro t s
  rw [show v+w+t=v+t+w by ring]
  exact TrajectoryProfiles.scalar_shift_all_distances H hfit s (v+t)

#print axioms gaussian_uniform_profile_recurrence
end
end GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
