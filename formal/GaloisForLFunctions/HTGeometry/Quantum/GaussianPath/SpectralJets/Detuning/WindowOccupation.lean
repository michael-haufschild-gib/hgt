import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ClockGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SignPacking.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliEarlyLateCircuitLaw

/-! # Finite observation windows for low circuit cost on one Gaussian path -/
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Every spectral sign can be used as a separated translate in the same
interval of length G. The finite observation error is therefore at most G. -/
theorem excursion_occupation_at_phase_horizon {n : ℕ} (hn : 1 ≤ n)
    (e : (Fin n → Bool) ≃ Fin ((2^n-1)+1)) (H : selfAdjoint (Reg n)) {G : ℝ} (hG : 0 ≤ G)
    (hent : atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) < ((2^(2^n-1):ℕ):ℝ))
    (hphase : ∀ c : Fin (2^n-1) → ℝ, ∃ t ∈ Icc 0 G, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80) :
    let r := excursionGateBudget n
    let W := translatedExcursionWidth n ‖H.val‖
    ∀ A T : ℝ, 0 ≤ T → (r+1:ℝ)^r * volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T)) ≤ T+G := by
  let d := 2^n-1
  have tubes := spectral_sign_visits_tube_occupation e H hG (fun x => by
    obtain ⟨t,ht,z,hz,hh⟩ := phase_interval_approaches_reflection e H 0 G hphase x
    exact ⟨t,ht,z,hz,hh.trans_lt (by norm_num)⟩)
  have hobs := circuit_window_occupation_of_tube_bound H tubes
  intro r₀ W₀ A T hT
  let r := excursionGateBudget n
  let W := translatedExcursionWidth n ‖(H : Reg n)‖
  let m := 1/(40*(‖(H : Reg n)‖+1))
  have hm : 0 < m := by dsimp [m]; positivity
  have hs : ‖(H : Reg n)‖*m ≤ 1/40 := by
    dsimp [m]; rw [mul_one_div,div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hcount : plateauGridCount W m = (r+1)^r := by
    change ⌈((((r+1)^r-1 : ℕ) : ℝ)*m)/m⌉₊ + 1 = _
    rw [mul_div_cancel_right₀ _ hm.ne',Nat.ceil_natCast]
    have hp : 0 < (r+1)^r := by positivity
    omega
  let M := (r+1)^r
  let Q := (atMostQuarterCircuitNet n r).card
  let V := volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T))
  have hQ : 0 < Q := by
    obtain ⟨x,hx,_⟩ := atMostQuarterCircuitNet_cover (TwoQubitCircuit.one n)
      (show (TwoQubitCircuit.one n).gateCount ≤ r from Nat.zero_le _)
    exact Finset.card_pos.mpr ⟨x,hx⟩
  have hM : 0 < M := by dsimp [M]; positivity
  have hsq : M*M*Q < 2^d := by
    rw [show M*M = (r+1)^(2*r) by rw [two_mul,pow_add]]
    exact translated_excursion_square_card hn hent
  have hsq' : (M:ℝ)*M*Q ≤ (2:ℝ)^d := by exact_mod_cast hsq.le
  have hvol := hobs r W m hm hs A T hT
  rw [hcount] at hvol
  change (2:ℝ)^d*V ≤ (M:ℝ)*Q*(T+G) at hvol
  have hv : 0 ≤ V := ENNReal.toReal_nonneg
  have hgoal : (M:ℝ)*V ≤ T+G := by
    apply le_of_mul_le_mul_left _ (show 0 < (M:ℝ)*Q by positivity)
    calc
      _ = ((M:ℝ)*M*Q)*V := by ring
      _ ≤ (2:ℝ)^d*V := mul_le_mul_of_nonneg_right hsq' hv
      _ ≤ _ := hvol
  simpa only [M,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hgoal

/-- On almost every infinite chain, all sufficiently long prefixes have the
same deterministic correction 2^(D^c) in the window occupation bound, for
every starting time and every observation length. -/
theorem gaussian_path_finite_window_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let r := excursionGateBudget N
      let W := translatedExcursionWidth N ‖H.val‖
      ∀ A T : ℝ, 0 ≤ T → (r+1:ℝ)^r * volume.real (circuitWindowHits H.val r W ∩ Icc A (A+T)) ≤
        T + (2:ℝ)^((2^N:ℕ)^c) := by
  obtain ⟨c,hG⟩ := derivativePhaseHorizon_double_upper
  refine ⟨c,?_⟩
  filter_upwards [gaussian_path_derivative_phase_filling] with ω hω
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hω,hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hfill he
  intro N u H r W A T hT
  obtain ⟨e,hphase⟩ := hfill
  apply excursion_occupation_at_phase_horizon (n := N) (by change 1 ≤ k+3; omega) e H (by positivity) he _ A T hT
  intro target
  obtain ⟨t,ht,hz⟩ := hphase 0 target
  exact ⟨t,⟨ht.1,(le_trans (by simpa only [zero_add] using ht.2) (hG k))⟩,hz⟩

#print axioms gaussian_path_finite_window_occupation
end
end GaloisForLFunctions.HTGeometry.SpectralJets
