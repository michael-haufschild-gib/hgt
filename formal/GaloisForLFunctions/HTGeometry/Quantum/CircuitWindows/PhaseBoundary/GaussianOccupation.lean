import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.UniformWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation

/-! # Exact finite-prefix physical occupation at every tolerance and every budget -/
open Set Filter MeasureTheory Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
open SharpOccupation
noncomputable section

/-- Almost surely each prefix has a limiting gate-count distribution at
every fixed physical error. Every length-dependent observation origin
gives the same limit, the Haar mass in this Hamiltonian's eigenbasis. -/
theorem gaussian_uniform_affordable_fraction :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      let V := hermitianEigenbasisUnitary H.2.isHermitian
      ∀ (s : ℕ) (ε : ℝ) (a : ℝ → ℝ),
        Tendsto (fun T => visitFraction H s ε (a T) (a T+T)) atTop
          (𝓝 (volume.real (projectiveContinuousCircuitCaptureTarget e V s ε))) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro N H e V s ε a
  let E := fun j => H.2.isHermitian.eigenvalues (e.symm j)
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  let f := RHTower.zeroProjectiveFrequency E
  have hi : MaximallyProjectiveEnergy E := maximallyProjectiveEnergy_equiv e.symm (hω k)
  have hset : finiteClockPhasePoint f ⁻¹' A = visitSet H s ε := by
    ext t
    exact (physical_circuit_approximation_iff_spectral_capture e H s ε t).symm
  have h := uniform_phase_fraction f (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hi)
    A (isClosed_projectiveContinuousCircuitCaptureTarget e V s ε).measurableSet (spectral_target_null e V E hi s ε) a
  simpa only [hset,visitFraction,add_sub_cancel_left] using h

#print axioms gaussian_uniform_affordable_fraction
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
