import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.ResiduePhases

/-! # Null relative boundaries for gate targets on translated frequency tori -/

open Set MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
noncomputable section

/-- The pulled-back affordable set has Haar-null boundary even when an
entire component lies at the specified approximation distance. -/
theorem residue_target_null {N d k : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin N → Bool) ℂ) (γ : Fin k → ℝ) (hf : FreeAtStep γ 1)
    (c : UnitAddTorus (Fin d)) (M : Fin d → Fin k → ℤ) (s : ℕ) (ε : ℝ) :
    volume (frontier ((fun x => c+torusIntegerHom M x) ⁻¹' projectiveContinuousCircuitCaptureTarget e V s ε))=0 := by
  let τ (t : ℝ) (x : UnitAddTorus (Fin k)) := finiteClockPhasePoint γ t+x
  let u (i : Fin d) := ∑ j, (M i j:ℝ)*γ j
  let E : Fin (d+1) → ℝ := Fin.cases 0 (fun j => -u j)
  have hE : RHTower.zeroProjectiveFrequency E=u := by
    funext j
    simp [E,RHTower.zeroProjectiveFrequency]
  have he (t : ℝ) : torusIntegerHom M (finiteClockPhasePoint γ t) = RHTower.projectivePhysicalPhaseFlow E t := by
    rw [←RHTower.finiteClockPhasePoint_zeroProjectiveFrequency,hE]
    exact (finiteClockPhasePoint_eq_torusIntegerHom u γ M (fun _ => rfl) t).symm
  have hi : RationallyIndependentFrequency γ := fun m hm => hf m 0 (by simp [hm])
  have hdense : DenseRange (finiteClockPhasePoint γ) := dense_range_finiteClockPhasePoint γ hi
  have hd (x : UnitAddTorus (Fin k)) : DenseRange (fun t => τ t x) :=
    (Homeomorph.addRight x).surjective.denseRange.comp hdense (Homeomorph.addRight x).continuous
  have hc : Continuous (fun p : UnitAddTorus (Fin k) × ℝ => τ p.2 p.1) :=
    ((finiteClockPhasePoint_continuous γ).comp continuous_snd).add continuous_fst
  let U := fun x => projectiveSpectralMatrix e V (c+torusIntegerHom M x)
  have hU : Continuous U := (continuous_projectiveSpectralMatrix e V).comp
    (continuous_const.add (continuous_torusIntegerHom M))
  have hset : ((fun x => c+torusIntegerHom M x) ⁻¹' projectiveContinuousCircuitCaptureTarget e V s ε) =
      {x | HasProjectiveCircuitApproximation N ε s (U x)} :=
    Set.ext fun x => mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε _
  rw [hset]
  apply PhaseBoundary.affordable_null_frontier volume τ hc.measurable
    (fun t => measurePreserving_add_left volume _) hd U hU _ s ε
  intro x i j
  have hx (t : ℝ) : U (τ t x) = projectiveSpectralMatrix e V
      (RHTower.projectivePhysicalPhaseFlow E t+(c+torusIntegerHom M x)) := by
    dsimp only [U,τ]
    rw [torusIntegerHom_add,he,add_left_comm]
  simp_rw [hx]
  exact PhaseBoundary.spectral_entries_analytic e V E (c+torusIntegerHom M x) i j

#print axioms residue_target_null
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
