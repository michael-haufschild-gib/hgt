import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliFirstThreshold
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.HorizonGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection

/-! # Deterministic absolute deadlines for first robust saturation and its first low return -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem two_pow_le_factorial_succ (n : ℕ) : 2^n ≤ (n+1).factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ,Nat.factorial_succ]
    exact (Nat.mul_le_mul ih (by omega : 2 ≤ n+1+1)).trans_eq (Nat.mul_comm _ _)

/-- The explicit all-labelings horizon itself exceeds 2^(2^(2^N−1)).
The exponent comes from multiplying the detuning over all energy labelings. -/
theorem pauliPrefixPhaseHorizon_factorial_floor (k : ℕ) (hk : 1 ≤ k) :
    (2:ℝ)^(2^(2^(k+3)-1):ℕ) ≤ pauliPrefixPhaseHorizon k := by
  let D := 2^(k+3)
  let d := D-1
  let e := prefixPhaseEnergyEquiv k
  let S := phaseClockModes e (1/80)
  let J := D.factorial
  let a : ℝ := (1/2:ℝ)^k / (1+(S.card:ℝ)*(2*(J:ℝ)))
  let V : ℝ := 1+((k+3:ℕ):ℝ)^2*∑ m ∈ S, ∑ i, |(m i:ℝ)|
  let F := nonconstantPacketIndexSet (phaseCubeFourierCutoff d (1/80)) d
  have hD : 0 < D := by dsimp [D]; positivity
  have hJ : 2^(D-1) ≤ J := by
    simpa only [Nat.sub_add_cancel hD] using two_pow_le_factorial_succ (D-1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha' : a ≤ 1/2 := by
    have hbase : (1/2:ℝ)^k ≤ 1/2 := by
      simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hk
    exact (div_le_self (by positivity) (le_add_of_nonneg_right (by positivity : 0 ≤ (S.card:ℝ)*(2*(J:ℝ))))).trans hbase
  have hV : 1 ≤ V := le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _))
  have hpair : (2:ℝ)^J*a^J ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (by norm_num) ha.le) (by linarith only [ha'])
  have hVpow := one_le_pow₀ (n := J-1) hV
  change (2:ℝ)^(2^(D-1):ℕ) ≤ 8*((F.card:ℝ)+1)/(a^J/V^(J-1))
  apply (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ).trans
  rw [div_div_eq_mul_div]
  apply (le_div_iff₀ (pow_pos ha J)).mpr
  apply hpair.trans
  have hF : 1 ≤ 8*((F.card:ℝ)+1) := by linarith only [Nat.cast_nonneg (α := ℝ) F.card]
  exact one_le_mul_of_one_le_of_one_le hF hVpow

#print axioms pauliPrefixPhaseHorizon_factorial_floor

/-- Almost surely, all sufficiently long prefixes have reached their first
robust exponential threshold by the deterministic phase horizon. Every
budget up to half the threshold budget then has an attained first return,
after the exponential exclusion interval and within one phase horizon of the crossing. -/
theorem gaussian_pauli_prefix_absolute_threshold_and_return :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := (2:ℝ)^(N/2)/(K*((N:ℝ)+1)^2)
      let G := pauliPrefixPhaseHorizon k
      ∃ σ : ℝ, B < σ ∧ σ ≤ G ∧ G ≤ (2:ℝ)^(2^(2^(2*N+9)):ℕ) ∧
        orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ t ∈ Icc (σ-B) (σ+B), ProjectiveCircuitSeparated N (1/10:ℝ) (P/2) (unitaryEvolution H.val t)) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+B < v ∧ v ≤ min (σ+G) ((σ+1)*(100:ℝ)^(2^N-1)) ∧
          HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) ∧
          ∀ t ∈ Ico σ v, ProjectiveCircuitSeparated N (1/10:ℝ) s (unitaryEvolution H.val t) := by
  obtain ⟨K,hK,hw⟩ := gaussian_pauli_prefix_first_threshold_and_return
  refine ⟨K,hK,?_⟩
  filter_upwards [hw,gaussian_path_eventually_calibrated_phase_filling] with ω hω hfill
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [hω,hfill,hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hfirst hf hent
  let N := k+3
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let P := nearHilbertContinuousCircuitBudget N
  let G := pauliPrefixPhaseHorizon k
  obtain ⟨σ,hB,he,hprior,hwindow,hreturns⟩ := hfirst
  have ph (a : ℝ) (c : Fin (2^N-1) → ℝ) : ∃ t ∈ Icc a (a+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i)) j-c j) < 1/80 := by
    simpa only [G,H,u,e,N,Function.comp_def] using hf a c
  obtain ⟨t,ht,hhard,_⟩ := phase_horizon_reaches_robust_threshold e H G (P := P) hent
    (fun c => by simpa only [zero_add] using ph 0 c)
  have hσt : σ ≤ t := by
    by_contra! h
    exact (not_lt_of_ge hhard) (hprior t ⟨ht.1,h⟩)
  refine ⟨σ,hB,hσt.trans ht.2,pauliPrefixPhaseHorizon_triple_upper k,he,hprior,hwindow,?_⟩
  intro s hs
  obtain ⟨v,hafter,hdir,hyes,hsep⟩ := hreturns s hs
  refine ⟨v,hafter,?_,hyes,hsep⟩
  refine le_min ?_ hdir
  obtain ⟨w,hw,hzero⟩ := phase_interval_contains_zero_gate e H σ (σ+G) (ph σ)
  refine le_trans ?_ hw.2
  by_contra! h
  obtain ⟨a,ha,C,hC,herr⟩ := hzero
  exact (not_lt_of_ge herr) (hsep w ⟨hw.1,h⟩ a ha C (hC.trans (Nat.zero_le s)))

#print axioms gaussian_pauli_prefix_absolute_threshold_and_return
end
end GaloisForLFunctions.HTGeometry
