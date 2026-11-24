import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.PhysicalClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation

/-! # The physical gate distribution on multiples of the first scalar return -/

open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
open AdaptiveSampling PrecisionReturns
noncomputable section

/-- Numbering the levels reverses the signs of the physical angular
frequencies. The corresponding integral characters change sign as well. -/
private theorem numbered_free {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (E : I → ℝ) (e : I ≃ Fin (d+1)) {τ : ℝ} (hf : FreeAtStep (projectiveFrequency E (e.symm 0)) τ) :
    FreeAtStep (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) τ := by
  let b := e.symm 0
  let r : Fin d ≃ {l : I // l≠b} := (finSuccAboveEquiv 0).trans
    (e.symm.subtypeEquiv (fun _ => not_congr e.symm.injective.eq_iff.symm))
  have hr (j : Fin d) : (r j).val=e.symm j.succ := by
    change e.symm ((0:Fin (d+1)).succAbove j)=_
    rw [Fin.zero_succAbove]
  intro m z hz
  let n (l : {l : I // l≠b}) := -m (r.symm l)
  have hd : finiteTorusCharacterDetuning n (projectiveFrequency E b)=
      finiteTorusCharacterDetuning m (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) := by
    unfold finiteTorusCharacterDetuning
    rw [←r.sum_comp (fun l => (n l:ℝ)*projectiveFrequency E b l)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [n,Equiv.symm_apply_apply,Int.cast_neg,projectiveFrequency,hr,
      RHTower.zeroProjectiveFrequency,Function.comp_apply,b]
    ring
  have hn := hf n z (hd.symm ▸ hz)
  funext j
  simpa only [n,Equiv.symm_apply_apply,Pi.zero_apply,neg_eq_zero] using congrFun hn (r j)

private theorem fraction {I : Type*} [Fintype I] (w : I → ℝ) (a v : ℝ) (hf : FreeAtStep w v)
    (A : Set (I → UnitAddCircle)) (hc : IsClosed A) (hb : volume (frontier A)=0) :
    Tendsto (fun j => (timeLaw a v j).real (finiteClockPhasePoint w ⁻¹' A)) atTop (𝓝 (volume.real A)) := by
  have hn : (finiteTorusHaarProbabilityMeasure I : Measure _) (frontier A)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (affine_phaseLaw w v a hf) hn
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at h
  have he (N : ℕ) : (integerClockPrefixLaw (fun j : ℕ => finiteClockPhasePoint w (a+(j:ℝ)*v)) N : Measure _) A =
      timeLaw a v N (finiteClockPhasePoint w ⁻¹' A) := by
    simp only [timeLaw,integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_apply (measurable_of_finite _) hc.measurableSet,
      Measure.map_apply (measurable_of_finite _) (hc.measurableSet.preimage (finiteClockPhasePoint_continuous w).measurable)]
    rfl
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (h.congr he)

/-- On every sufficiently long prefix of a typical frozen chain, the
gate-count distribution on multiples of the first scalar return after
the first robust crossing equals the continuous-time Haar distribution.
The sampling origin, budget and observation error are arbitrary. -/
theorem gaussian_first_scalar_clock_gate_law :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      let V := hermitianEigenbasisUnitary H.2.isHermitian
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        ∀ (a : ℝ) (s : ℕ) (ε : ℝ),
          Tendsto (fun j => (timeLaw a v j).real (SharpOccupation.visitSet H s ε)) atTop
            (𝓝 (volume.real (projectiveContinuousCircuitCaptureTarget e V s ε))) := by
  filter_upwards [gaussian_first_crossing_scalar_clock,gaussian_path_all_prefixes_maximally_projective]
    with ω hclock hmax
  filter_upwards [hclock] with k hk
  intro N H P e V
  obtain ⟨σ,hσ,hc,hb,hfree⟩ := hk
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro v a s ε
  let E := energy ω k
  let w := RHTower.zeroProjectiveFrequency (E ∘ e.symm)
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  have hf : FreeAtStep w v := numbered_free E e (hfree (e.symm 0)).1
  have hn := PhaseBoundary.spectral_target_null e V (E ∘ e.symm)
    (maximallyProjectiveEnergy_equiv e.symm (hmax k)) s ε
  have he : finiteClockPhasePoint w ⁻¹' A=SharpOccupation.visitSet H s ε := by
    ext t
    exact (physical_circuit_approximation_iff_spectral_capture e H s ε t).symm
  rw [←he]
  exact fraction w a v hf A (isClosed_projectiveContinuousCircuitCaptureTarget e V s ε) hn

#print axioms gaussian_first_scalar_clock_gate_law
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
