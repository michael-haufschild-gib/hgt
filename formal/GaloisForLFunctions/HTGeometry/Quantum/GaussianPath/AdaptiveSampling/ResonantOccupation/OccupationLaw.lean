import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.ResidueTargets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ResonantOccupation.ResidueCounts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ArcLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum

/-! # Exact gate frequencies on every affine lattice of every finite Hamiltonian -/

open Set Filter MeasureTheory Topology Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
open EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

/-- Every translated lattice, including resonant lattices, has a
limiting circuit-cost distribution. Its affordable fractions are
averages of finitely many Haar masses on parametrized subtori. -/
theorem spectral_gate_frequency {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin N → Bool) ℂ) (w : Fin d → ℝ) (a τ : ℝ) :
    ∃ (L : ℕ) (_ : 0<L) (k : ℕ) (M : Fin d → Fin k → ℤ),
      ∀ (s : ℕ) (ε : ℝ), let A := projectiveContinuousCircuitCaptureTarget e V s ε
        let c (b : ℕ) := finiteClockPhasePoint w (a+(b:ℝ)*τ)
        Tendsto (fun n => (timeLaw a τ n).real (finiteClockPhasePoint w ⁻¹' A)) atTop
          (𝓝 ((∑ b ∈ range L, volume.real ((fun x => c b+torusIntegerHom M x) ⁻¹' A))/L)) := by
  classical
  obtain ⟨L,hL,k,γ,M,hf,hparam⟩ := exists_residue_phases w a τ
  refine ⟨L,hL,k,M,?_⟩
  intro s ε A c
  let hit (n : ℕ) := c n∈A
  let B (b : ℕ) := (fun x => c b+torusIntegerHom M x) ⁻¹' A
  let v (b : ℕ) := volume.real (B b)
  have hA : IsClosed A := isClosed_projectiveContinuousCircuitCaptureTarget e V s ε
  have hB (b : ℕ) : IsClosed (B b) := hA.preimage (continuous_const.add (continuous_torusIntegerHom M))
  have hphase : Tendsto (integerClockPrefixLaw (fun n : ℕ => finiteClockPhasePoint γ (n:ℝ)))
      atTop (𝓝 (finiteTorusHaarProbabilityMeasure (Fin k))) := by
    simpa only [zero_add,mul_one] using affine_phaseLaw γ 1 0 hf
  have hr (b : ℕ) (_ : b<L) : Tendsto (fun n : ℕ => (Nat.count (fun j => hit (L*j+b)) n:ℝ)/n)
      atTop (𝓝 (v b)) := by
    have hn : (finiteTorusHaarProbabilityMeasure (Fin k) : Measure _) (frontier (B b))=0 := by
      rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
      exact residue_target_null e V γ hf (c b) M s ε
    have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hphase hn
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hh
    have he : (fun j : ℕ => finiteClockPhasePoint γ (j:ℝ)∈B b)=(fun j => hit (L*j+b)) := by
      funext j
      change (c b+torusIntegerHom M (finiteClockPhasePoint γ j)∈A)=(c (L*j+b)∈A)
      rw [←hparam]
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh).congr
    intro n
    change (integerClockPrefixLaw (fun j : ℕ => finiteClockPhasePoint γ (j:ℝ)) n : Measure _).real (B b)=_
    rw [prefix_count _ _ (hB b).measurableSet]
    simp only [he,Nat.cast_add,Nat.cast_one]
  have hv := (density_of_residue_densities hit hL v hr).comp (tendsto_add_atTop_nat 1)
  apply hv.congr
  intro n
  rw [timeLaw,prefix_count _ _ (hA.measurableSet.preimage (finiteClockPhasePoint_continuous w).measurable)]
  dsimp only [Function.comp_apply]
  simp only [Nat.cast_add,Nat.cast_one,hit,c,Set.mem_preimage]

/-- For an arbitrary finite qubit Hamiltonian, each physical gate
budget and error has a limiting fraction on every affine lattice. -/
theorem physical_gate_frequency {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ)) (a τ : ℝ) (s : ℕ) (ε : ℝ) :
    ∃ p : ℝ, Tendsto (fun n => (timeLaw a τ n).real (SharpOccupation.visitSet H s ε)) atTop (𝓝 p) := by
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := fun j => H.2.isHermitian.eigenvalues (e.symm j)
  let w := RHTower.zeroProjectiveFrequency E
  obtain ⟨L,hL,k,M,h⟩ := spectral_gate_frequency e V w a τ
  have he : finiteClockPhasePoint w ⁻¹' projectiveContinuousCircuitCaptureTarget e V s ε =
      SharpOccupation.visitSet H s ε := Set.ext fun t => (physical_circuit_approximation_iff_spectral_capture e H s ε t).symm
  rw [←he]
  exact ⟨_,h s ε⟩

#print axioms physical_gate_frequency
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
