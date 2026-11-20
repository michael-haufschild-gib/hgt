import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ReferenceGrid

/-! # Absolute deadlines for long hard intervals on the Gaussian Pauli path -/
open Set Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem phase_horizon_contains_excursion {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (a G W mesh : ℝ) (hm : 0 < mesh) (hspeed : ‖H.val‖*mesh ≤ 1/40)
    (hcard : plateauGridCount W mesh*(atMostQuarterCircuitNet n s).card < 2^d)
    (hphase : ∀ c : Fin d → ℝ, ∃ t ∈ Icc a (a+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) :
    ∃ u ∈ Icc a (a+G), (∀ t ∈ Icc u (u+W), ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution H.val t)) ∧
      HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution H.val (2*u)) := by
  let U (j : Fin (plateauGridCount W mesh)) : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    ⟨unitaryEvolution H.val ((j.val:ℝ)*mesh),unitaryEvolution_mem_unitary H.2 _⟩
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  obtain ⟨x,hx⟩ := exists_reflection_avoiding_translated_circuits e V U hcard
  let J := anchoredSpectralBooleanReflection e V x
  obtain ⟨u,hu,z,hz,hclose⟩ := phase_interval_approaches_reflection e H a (a+G) hphase x
  change ‖unitaryEvolution H.val u-z • J‖ ≤ 1/80 at hclose
  refine ⟨u,hu,circuit_window_of_reference_grid H J z u W mesh hz hm hspeed (hclose.trans (by norm_num)) hx,?_⟩
  let w : Circle := ⟨z,by change z ∈ Metric.sphere (0:ℂ) 1; simpa using hz⟩
  obtain ⟨c,hc,C,hC,he⟩ := spectral_sign_doubled_time_zero_gate e V x H u w
  refine ⟨c,hc,C,hC,he.trans ?_⟩
  change 2*‖unitaryEvolution H.val u-z • J‖ ≤ (1/10:ℝ)
  linarith only [hclose]

/-- Every nonnegative start has an explicitly bounded wait to a full hard
interval. Its width is below its starting time. Each affordable budget has
an attained first subsequent visit between its end and twice its start. -/
theorem gaussian_pauli_prefix_dated_excursions :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let r := excursionGateBudget N
      let W := translatedExcursionWidth N ‖H.val‖
      ∀ a : ℝ, 0 ≤ a → ∃ u ∈ Icc a (a+pauliPrefixPhaseHorizon k), W < u ∧
        (∀ t ∈ Icc u (u+W), ProjectiveCircuitSeparated N (1/10:ℝ) r (unitaryEvolution H.val t)) ∧
        HasProjectiveCircuitApproximation N (1/10:ℝ) 0 (unitaryEvolution H.val (2*u)) ∧
        ∀ s ≤ r, ∃ v ∈ Ioc (u+W) (2*u), HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) ∧
          ∀ t ∈ Ico u v, ProjectiveCircuitSeparated N (1/10:ℝ) s (unitaryEvolution H.val t) := by
  filter_upwards [gaussian_path_eventually_calibrated_phase_filling] with ω hω
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hω,hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier] with k hf hent
  let N := k+3
  let u₀ := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u₀,isSelfAdjoint_pathHamiltonian _⟩
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  let mesh := 1/(40*(‖H.val‖+1))
  have hm : 0 < mesh := by dsimp [mesh]; positivity
  have hs : ‖H.val‖*mesh ≤ 1/40 := by
    dsimp [mesh]; rw [mul_one_div,div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hcount : plateauGridCount W mesh = (r+1)^r := by
    change ⌈((((r+1)^r-1:ℕ):ℝ)*mesh)/mesh⌉₊+1 = _
    rw [mul_div_cancel_right₀ _ hm.ne',Nat.ceil_natCast]
    have : 0 < (r+1)^r := by positivity
    omega
  have hc : plateauGridCount W mesh*(atMostQuarterCircuitNet N r).card < 2^(2^N-1) := by
    rw [hcount]
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < r+1) (by omega : r ≤ 2*r))).trans_lt
      (translated_excursion_square_card (by dsimp [N]; omega : 1 ≤ N) hent)
  intro _ _ _ _ a ha
  have hph (c : Fin (2^N-1) → ℝ) : ∃ t ∈ Icc a (a+pauliPrefixPhaseHorizon k), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80 := by
    simpa only [N,H,u₀,e,Function.comp_def] using hf a c
  obtain ⟨u,hu,hh,hzero⟩ := phase_horizon_contains_excursion e H a (pauliPrefixPhaseHorizon k) W mesh hm hs hc hph
  have hu0 : 0 ≤ u := ha.trans hu.1
  have hafter : W < u := by
    by_contra! h
    obtain ⟨z,hz,C,hC,he⟩ := hzero
    exact (not_lt_of_ge he) (hh (2*u) ⟨by linarith only [hu0],by linarith only [h]⟩ z hz C (hC.trans (Nat.zero_le r)))
  refine ⟨u,hu,hafter,hh,hzero,?_⟩
  intro s hsr
  obtain ⟨v,hv,he,hprior⟩ := projective_first_circuit_visit_deadline e H u s
  refine ⟨v,⟨?_,?_⟩,he,hprior⟩
  · by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := he
    exact (not_lt_of_ge herr) (hh v ⟨hv.1,h⟩ z hz C (hC.trans hsr))
  · by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := hzero
    exact (not_lt_of_ge herr) (hprior (2*u) ⟨by linarith only [hu0],h⟩ z hz C (hC.trans (Nat.zero_le s)))

#print axioms gaussian_pauli_prefix_dated_excursions
end
end GaloisForLFunctions.HTGeometry
