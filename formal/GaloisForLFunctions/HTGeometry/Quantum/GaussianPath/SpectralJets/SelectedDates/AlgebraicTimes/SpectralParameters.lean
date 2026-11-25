import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.CoefficientField
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.PauliCoefficients

/-! # Independence of sorted spectral phases at algebraic coupling-dependent times -/

open Set MeasureTheory Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
open ExactContacts
noncomputable section

/-- All nonzero times algebraic over a typical coupling vector retain
independent relative phases, even when that vector selects the time. -/
theorem ae_sorted_algebraic_time_phases (N : ℕ) (b : Fin (2^N)) :
    ∀ᵐ x ∂(volume : Measure (Fin (Fintype.card (ChainLabel N)) → ℝ)),
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
      x∈simpleEnsembleLocus (chainPauliFin_isHermitian N) → MaximallyProjectiveEnergy E →
      ∀ t : ℝ, t≠0 → IsAlgebraic (parameterField x) t →
        AlgebraicIndependent (complexParameterField x) (fun i : {j // j≠b} => energyPhase (E i.val-E b) t) := by
  let P := chainPauliFin_isHermitian N
  let E := sortedEnsembleSpectrum P
  let w (i : {j // j≠b}) (x : Fin (Fintype.card (ChainLabel N)) → ℝ) := E x i.val-E x b
  have ha i : AnalyticOnNhd ℝ (w i) (simpleEnsembleLocus P) := fun x hx =>
    (analyticAt_sortedEnsembleSpectrum P hx i.val).sub (analyticAt_sortedEnsembleSpectrum P hx b)
  have halg (q : Fin (Fintype.card (ChainLabel N)) → ℚ) (_ : (fun i => (q i:ℝ))∈simpleEnsembleLocus P)
      (i : {j // j≠b}) : IsAlgebraic ℚ ((w i (fun j => (q j:ℝ)):ℝ):ℂ) := by
    dsimp only [w]
    rw [Complex.ofReal_sub]
    exact (rational_pauli_energy N q i.val).sub (rational_pauli_energy N q b)
  filter_upwards [ae_phase_polynomials (isOpen_simpleEnsembleLocus P) w ha halg] with x hx
  intro S hsimple hmax t ht hta
  apply independent_of_parameter_polynomials x
  exact fun p => hx hsimple (maximallyProjectiveEnergy_projectiveFrequency_independent _ hmax b) p t ht hta

#print axioms ae_sorted_algebraic_time_phases
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
