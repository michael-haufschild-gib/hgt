import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.FineReturns.SortedGaps
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.FineReturns.IndexComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # The physical precision exponent on a shifted first-wait lattice -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
open PrecisionReturns PrescribedTimes ResonantReturns
noncomputable section

/-- A sorted spectral gap exponent gives the physical first-index
exponent on the same clock, for every disconnected gate budget. -/
theorem gaussian_sorted_index_comparison :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let x := fun i => u (pathCoeffEquiv (k+1) i)
      ∀ τ D : ℝ, Tendsto (fun r => log (firstHit (fun i => τ*qubitPathDiscreteFrequency k x i) r)/log (1/r))
        (𝓝[>] (0:ℝ)) (𝓝 D) → ∀ j : ℕ, j+1<N →
          Tendsto (fun ε => log (firstIndex H τ j ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 D) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,
    DisconnectedReturns.gaussian_disconnected_scalar_return] with ω hmax hscalar k
  intro N u H x τ D hrate j hj
  obtain ⟨A,hA,hctrl⟩ := hscalar (k+1)
  obtain ⟨p,hp⟩ := SpectralJets.physical_sorted_order k ω (hmax k).injective
  let e := p.trans (prefixPhaseEnergyEquiv k)
  apply index_exponent_of_gaps H e τ j hA (fun t ε => hctrl t ε j (by dsimp [N] at hj; omega))
  let E := H.2.isHermitian.eigenvalues
  change ∀ a, E a = qubitPathSortedEnergy k x (p a) at hp
  let β (i : Fin (2^N-1)) := τ*(E (e.symm i.succ)-E (e.symm 0))/(2*π)
  have hs (i : Fin ((2^N-1)+1)) : E (e.symm i)=qubitPathSortedEnergy k x ((prefixPhaseEnergyEquiv k).symm i) := by
    simpa only [e,Equiv.symm_trans_apply,p.apply_symm_apply] using hp (e.symm i)
  have he : β=fun i => τ*qubitPathDiscreteFrequency k x i := by
    funext i
    rw [show β i=τ*(E (e.symm i.succ)-E (e.symm 0))/(2*π) from rfl,hs,hs]
    change τ*(qubitPathSortedEnergy k x (qubitPathRecurrenceIndex k i)-
      qubitPathSortedEnergy k x (qubitPathRecurrenceAnchor k))/(2*π)=_
    dsimp only [qubitPathDiscreteFrequency,anchoredGapMap]
    ring
  change Tendsto (fun r => log (firstHit β r)/log (1/r)) _ _
  rw [he]
  exact hrate

/-- After a prescribed nonzero shift of the actual first physical wait,
the first positive clock index admitting a fit below N−1 gates has
precision exponent D−1, simultaneously at all such fine budgets. -/
theorem gaussian_shifted_wait_first_index (h : ℕ → ℝ) (hh : ∀ k, h k≠0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let x := fun i => u (pathCoeffEquiv (k+1) i)
      ∀ l s : ℕ, let τ := crossingWait (k+1) l s x+h k
        0<τ → ∀ j : ℕ, j+1<N →
          Tendsto (fun ε => log (firstIndex H τ j ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-1:ℕ):ℝ)) := by
  filter_upwards [gaussian_shifted_gap_rate h hh,gaussian_sorted_index_comparison] with ω hr hc k
  intro N u H x l s τ hτ
  exact hc k τ _ (hr k l s hτ)

#print axioms gaussian_shifted_wait_first_index
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
