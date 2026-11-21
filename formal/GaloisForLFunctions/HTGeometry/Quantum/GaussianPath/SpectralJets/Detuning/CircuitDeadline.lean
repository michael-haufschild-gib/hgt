import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ClockGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliFirstThreshold

/-! # Doubly exponential upper deadline for the first low-circuit return -/

open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Almost surely on all sufficiently long prefixes of the same Gaussian Pauli
chain, the first robust exponential-budget crossing occurs by 2^(D^c).
For every budget at most half the crossing budget, the first affordable
return after that crossing also occurs within an additional 2^(D^c). -/
theorem gaussian_path_double_exponential_first_return_upper :
    ∃ c : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := (2:ℝ)^(N/2)/(K*((N:ℝ)+1)^2)
      let G := (2:ℝ)^(D^c)
      ∃ σ : ℝ, B < σ ∧ σ ≤ G ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ t ∈ Icc (σ-B) (σ+B), ProjectiveCircuitSeparated N (1/10:ℝ) (P/2) (unitaryEvolution H.val t)) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+B < v ∧ v ≤ min (σ+G) ((σ+1)*(100:ℝ)^(D-1)) ∧
          HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) ∧
          ∀ t ∈ Ico σ v, ProjectiveCircuitSeparated N (1/10:ℝ) s (unitaryEvolution H.val t) := by
  obtain ⟨c,hG⟩ := derivativePhaseHorizon_double_upper
  obtain ⟨K,hK,hw⟩ := gaussian_pauli_prefix_first_threshold_and_return
  refine ⟨c,K,hK,?_⟩
  filter_upwards [hw,gaussian_path_derivative_phase_filling] with ω hfirst hfill
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hfirst,hfill,hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hk hf hent
  intro N D u H P B G
  obtain ⟨e,he⟩ := hf
  have ph (a : ℝ) (c' : Fin (D-1) → ℝ) : ∃ t ∈ Icc a (a+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c' j) < 1/80 := by
    obtain ⟨t,ht,hz⟩ := he a c'
    exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl (hG k))⟩,hz⟩
  obtain ⟨σ,hB,heq,hprior,hwindow,hreturns⟩ := hk
  obtain ⟨t,ht,hhard,_⟩ := phase_horizon_reaches_robust_threshold e H G (P := P) hent
    (fun z => by simpa only [zero_add] using ph 0 z)
  have hσ : σ ≤ t := by
    by_contra! h
    exact (not_lt_of_ge hhard) (hprior t ⟨ht.1,h⟩)
  refine ⟨σ,hB,hσ.trans ht.2,heq,hprior,hwindow,?_⟩
  intro s hs
  obtain ⟨v,hafter,hdir,hyes,hsep⟩ := hreturns s hs
  refine ⟨v,hafter,le_min ?_ hdir,hyes,hsep⟩
  obtain ⟨w,hw,hzero⟩ := phase_interval_contains_zero_gate e H σ (σ+G) (ph σ)
  apply le_trans ?_ hw.2
  by_contra! h
  obtain ⟨a,ha,C,hC,herr⟩ := hzero
  exact (not_lt_of_ge herr) (hsep w ⟨hw.1,h⟩ a ha C (hC.trans (Nat.zero_le s)))

#print axioms gaussian_path_double_exponential_first_return_upper
end
end GaloisForLFunctions.HTGeometry.SpectralJets
