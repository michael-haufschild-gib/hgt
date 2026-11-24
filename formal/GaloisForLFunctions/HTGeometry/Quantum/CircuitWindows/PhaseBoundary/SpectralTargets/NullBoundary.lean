import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.AnalyticTarget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralFlow

/-! # Haar-null boundaries of physical circuit capture sets in spectral coordinates -/

open Set MeasureTheory Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

/-- The boundary of every physical affordability set is Haar-null on a full-rank spectral torus. -/
theorem spectral_target_null {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
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

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
