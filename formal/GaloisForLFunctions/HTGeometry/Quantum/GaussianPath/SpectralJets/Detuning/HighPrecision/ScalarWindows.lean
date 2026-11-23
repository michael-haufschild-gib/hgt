import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.PhaseWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection

/-! # Uniform physical recurrence to a scalar at inverse-exponential error -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
private abbrev Register (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
noncomputable section

/-- Every origin on the same frozen trajectory reaches an empty-circuit
visit at error two to minus the Hilbert dimension within a doubly
exponential horizon. The origin may depend on the entire draw. -/
theorem gaussian_fine_scalar_windows :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∀ a : ℝ, ∃ t ∈ Icc a (a+(2:ℝ)^(D^C)),
        HasProjectiveCircuitApproximation N (1/(2:ℝ)^D) 0 (unitaryEvolution H t) := by
  obtain ⟨C,hC⟩ := gaussian_bit_phase_filling _ PolynomialInDimension.dim
  refine ⟨C,?_⟩
  filter_upwards [hC] with ω hω
  filter_upwards [hω] with k hk
  intro N D H a
  let A : selfAdjoint (Register N) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  obtain ⟨e,he⟩ := hk
  exact phase_interval_zero_gate_at_error (by positivity : 0 ≤ 1/(2:ℝ)^D) e A a _ (he a)

#print axioms gaussian_fine_scalar_windows
end
end GaloisForLFunctions.HTGeometry.SpectralJets.HighPrecision
