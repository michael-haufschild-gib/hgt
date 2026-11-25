import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SelectedSchedule
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.NumberedCharacters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.GateDistribution
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary

/-! # Larger-prefix gate occupation along a schedule fixed by other couplings -/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open AdaptiveSampling SharpOccupation
noncomputable section

/-- A character of the zero-anchored physical phases is a balanced action
on the eigenvalues, with the minus sign from exp(−itH) on non-anchor rows. -/
private theorem numbered_action {d : ℕ} (E : Fin (d+1) → ℝ) (m : Fin d → ℤ) (hm : m≠0) :
    ∃ c : Fin (d+1) → ℤ, c≠0 ∧ (∑ i, c i)=0 ∧
      (∑ i, (c i:ℝ)*E i)=finiteTorusCharacterDetuning m (RHTower.zeroProjectiveFrequency E) := by
  refine ⟨numberedPacket m,?_,numberedPacket_sum m,numberedPacket_action E m⟩
  intro h
  apply hm
  funext i
  simpa only [numberedPacket,Fin.cases_succ,neg_eq_zero,Pi.zero_apply] using congrFun h i.succ

/-- For every physical gate budget and every fixed tolerance, the frequency
on a smaller-prefix schedule equals the continuous-time frequency on the
larger register, even though the two Hamiltonians share their couplings. -/
theorem gaussian_selected_gate_law (k : ℕ) (s : PathPauliDisorder → ℕ → ℝ)
    (hs : ∀ j, Measurable (fun η => s η j)) (hsep : ∀ η j, s η j+1 ≤ s η (j+1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (b : ℕ) (ε : ℝ), ∃ p : ℝ,
        (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction H b ε (u T) (u T+T)) atTop (𝓝 p)) ∧
        Tendsto (fun M => (integerClockPrefixLaw (s (eraseTerminal k ω)) M : Measure ℝ).real
          (visitSet H b ε)) atTop (𝓝 p) := by
  classical
  filter_upwards [gaussian_selected_actions k s hs hsep,gaussian_path_all_prefixes_maximally_projective]
    with ω hω hspec
  intro N H b ε
  let d := 2^N-1
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,d]
    have hp := Nat.two_pow_pos N
    omega))
  let E := H.2.isHermitian.eigenvalues ∘ e.symm
  let f := RHTower.zeroProjectiveFrequency E
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := projectiveContinuousCircuitCaptureTarget e V b ε
  let t := s (eraseTerminal k ω)
  have hw : Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint f (t j))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
    apply haar_of_clock_cancellation
    intro m hm
    obtain ⟨c,hc,hbal,hdet⟩ := numbered_action E m hm
    let q := c ∘ e
    have hn : q≠0 := by
      intro hz
      apply hc
      funext i
      simpa only [q,Function.comp_apply,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun hz (e.symm i)
    have hb := (Equiv.sum_comp e c).trans hbal
    have he : (∑ i, (q i:ℝ)*H.2.isHermitian.eigenvalues i)=finiteTorusCharacterDetuning m f := by
      refine Eq.trans ?_ hdet
      simpa only [q,E,Function.comp_apply,Equiv.symm_apply_apply] using Equiv.sum_comp e (fun i => (c i:ℝ)*E i)
    rw [←he]
    exact hω q hn hb
  have hmax : MaximallyProjectiveEnergy E := (hspec k).comp_equiv e.symm
  have hA := (isClosed_projectiveContinuousCircuitCaptureTarget e V b ε).measurableSet
  have hbd := PhaseBoundary.spectral_target_null e V E hmax b ε
  have ha : finiteClockPhasePoint f ⁻¹' A=visitSet H b ε :=
    Set.ext fun u => (physical_circuit_approximation_iff_spectral_capture e H b ε u).symm
  refine ⟨volume.real A,fun u => ?_,?_⟩
  · have ht := PhaseBoundary.uniform_phase_fraction f
      (RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent E hmax) A hA hbd u
    simpa only [ha,visitFraction,add_sub_cancel_left] using ht
  · rw [←ha]
    exact ShiftedWaits.sampled_fraction f t hw A hA hbd

#print axioms gaussian_selected_gate_law
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
