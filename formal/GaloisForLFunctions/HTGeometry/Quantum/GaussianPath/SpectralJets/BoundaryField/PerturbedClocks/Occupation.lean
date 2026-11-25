import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.GateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnClock

/-! # Perturbing one field while keeping the original physical observation dates -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
open AdaptiveSampling NestedPrefixes SharpOccupation
noncomputable section

/-- Adding z to the longitudinal field of the terminal spin changes no
other term of the physical generator. -/
abbrev shiftedGenerator (ω : PathPauliDisorder) (k : ℕ) (z : ℝ) : selfAdjoint (Register (k+3)) :=
  ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩

/-- Choose any separated observation dates after seeing the entire
original Hamiltonian. Almost every additive change of just its terminal
field gives the changed register its ordinary gate law on those dates. -/
theorem gaussian_changed_field_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ t : ℕ → ℝ,
      (∀ i, t i+1 ≤ t (i+1)) → ∀ᵐ z : ℝ,
        let H := shiftedGenerator ω k z
        MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
        ∀ (b : ℕ) (ε : ℝ), ∃ p : ℝ,
          (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H b ε (u T) (u T+T)) atTop (𝓝 p)) ∧
          Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real (visitSet H b ε)) atTop (𝓝 p) := by
  filter_upwards [gaussian_boundary_null_frequencies] with ω hω k t ht
  let S := {u : ℝ | ¬Tendsto (clockCharacterMean t u) atTop (𝓝 0)}
  have hS : volume S=0 := measure_eq_zero_iff_ae_notMem.mpr
    ((ae_separated_clock_exp t ht).mono fun _ h => not_not_intro h)
  filter_upwards [hω k S hS,hω k {0} (measure_singleton _)] with z hcancel hn
  let H := shiftedGenerator ω k z
  have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := by
    intro m hm he
    by_contra h
    exact hn m h hm he
  exact ⟨hmax,gate_law_of_balanced_clock H t hmax (fun m hm hb => not_not.mp (hcancel m hm hb))⟩

/-- At the original register's own successive 1/10 dip dates, starting
with its first low visit after its 9/80 crossing, almost every one-field
perturbation has its unconditioned long-time gate frequencies. -/
theorem gaussian_changed_field_on_return_records :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k P s : ℕ,
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let t := returnClock (k+1) P s x
      ∀ᵐ z : ℝ, let H := shiftedGenerator ω k z
        ∀ (b : ℕ) (ε : ℝ), ∃ p : ℝ,
          (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H b ε (u T) (u T+T)) atTop (𝓝 p)) ∧
          Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real (visitSet H b ε)) atTop (𝓝 p) := by
  filter_upwards [gaussian_changed_field_clock] with ω hω k P s
  intro x t
  exact (hω k t (returnClock_separated _ _ _ x)).mono fun _ h => h.2

#print axioms gaussian_changed_field_clock
#print axioms gaussian_changed_field_on_return_records
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
