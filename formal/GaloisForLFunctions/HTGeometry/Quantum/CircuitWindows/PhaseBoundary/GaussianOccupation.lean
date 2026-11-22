import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.AnalyticTarget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralFlow
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

private theorem spectral_target_null {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin N → Bool) ℂ) (E : Fin (d+1) → ℝ)
    (hE : MaximallyProjectiveEnergy E) (s : ℕ) (ε : ℝ) :
    volume (frontier (projectiveContinuousCircuitCaptureTarget e V s ε))=0 := by
  let τ (t : ℝ) (x : Fin d → UnitAddCircle) := RHTower.projectivePhysicalPhaseFlow E t+x
  have hc : Continuous (fun p : (Fin d → UnitAddCircle) × ℝ => τ p.2 p.1) :=
    ((RHTower.uniformContinuous_projectivePhysicalPhaseFlow E).continuous.comp continuous_snd).add continuous_fst
  have hd (x : Fin d → UnitAddCircle) : DenseRange (fun t => τ t x) :=
    (Homeomorph.addRight x).surjective.denseRange.comp (RHTower.denseRange_projectivePhysicalPhaseFlowHom E hE)
      (Homeomorph.addRight x).continuous
  have heq : projectiveContinuousCircuitCaptureTarget e V s ε =
      {x | HasProjectiveCircuitApproximation N ε s (projectiveSpectralMatrix e V x)} :=
    Set.ext fun x => mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε x
  rw [heq]
  exact affordable_null_frontier volume τ hc.measurable (fun t => measurePreserving_add_left volume _) hd
    _ (continuous_projectiveSpectralMatrix e V) (spectral_entries_analytic e V E) s ε

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
