import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WindowOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WaitingWidth

/-! # Two-sided first waiting times from typical observation times -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- From every origin the first affordable visit occurs within G. In every
observation interval of length at least G, outside a fraction at most
2/2^⌊D/1024⌋, all budgets through half the exponential threshold have a
first waiting time strictly greater than 2^⌊D/2048⌋. -/
theorem gaussian_path_typical_first_wait :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let r := excursionGateBudget N
      let G := (2:ℝ)^(D^c)
      (∀ a : ℝ, ∀ s : ℕ, firstCircuitVisit H s a ≤ a+G) ∧
      ∀ A T : ℝ, G ≤ T →
        (2:ℝ)^(D/1024) * volume.real
          ({a | ∃ s ≤ r, firstCircuitVisit H s a ≤ a+(2:ℝ)^(D/2048)} ∩ Icc A (A+T)) ≤ 2*T := by
  obtain ⟨c,hbound⟩ := derivativePhaseHorizon_double_upper
  refine ⟨c,?_⟩
  filter_upwards [gaussian_path_derivative_phase_filling,gaussian_path_eventual_double_exponential_width] with ω hf hw
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hf,hw,eventually_ge_atTop 64,hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hf hw hk hent
  intro N D u H r G
  obtain ⟨e,he⟩ := hf
  have hphase (a : ℝ) (z : Fin (D-1) → ℝ) : ∃ t ∈ Icc a (a+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-z j) < 1/80 := by
    obtain ⟨t,ht,hh⟩ := he a z
    exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl (hbound k))⟩,hh⟩
  constructor
  · intro a s
    change a ∈ {b | firstCircuitVisit H s b ≤ b+G}
    rw [← circuitWindowHits_eq_firstVisit]
    obtain ⟨t,ht,z,hz,C,hC,herr⟩ := phase_interval_contains_zero_gate e H a (a+G) (hphase a)
    exact ⟨t,ht,z,hz,C,hC.trans (Nat.zero_le s),herr⟩
  intro A T hT
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let W := translatedExcursionWidth N ‖H.val‖
  have hsub : {a | ∃ s ≤ r, firstCircuitVisit H s a ≤ a+(2:ℝ)^(D/2048)} ⊆ circuitWindowHits H.val r W := by
    rintro a ⟨s,hs,hearly⟩
    have ha : a ∈ {b | firstCircuitVisit H s b ≤ b+W} := hearly.trans (add_le_add le_rfl hw)
    rw [← circuitWindowHits_eq_firstVisit] at ha
    obtain ⟨t,ht,z,hz,C,hC,herr⟩ := ha
    exact ⟨t,ht,z,hz,C,hC.trans hs,herr⟩
  have hv := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc A (A+T)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hM : (2:ℝ)^(D/1024) ≤ ((r:ℝ)+1)^r := by
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  have ho := excursion_occupation_at_phase_horizon (n := N) (by change 1 ≤ k+3; omega) e H hG hent
    (fun z => by simpa only [zero_add] using hphase 0 z) A T (hG.trans hT)
  exact ((mul_le_mul hM hv ENNReal.toReal_nonneg (by positivity)).trans ho).trans (by linarith only [hT])

#print axioms gaussian_path_typical_first_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets
