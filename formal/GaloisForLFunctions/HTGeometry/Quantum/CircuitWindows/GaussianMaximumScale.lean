import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMeanReturns

/-! # Exponential scale of the actual fixed-error maximum and typical cost -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Above a fixed register size the fifth power of the first excluded
budget dominates the uniform synthesis bound. -/
private theorem cap_le_excursion_power {n : ℕ} (hn : 256 ≤ n) :
    160*(2*n+1)*16^n ≤ (excursionGateBudget n + 1)^5 := by
  let F := 128*(n+1)
  let r := excursionGateBudget n
  have hF : 0 < F := by dsimp [F]; positivity
  have hr : r = 2^n/F := by
    change (2^n/(64*(n+1)))/2 = _
    rw [Nat.div_div_eq_div_mul,show 64*(n+1)*2 = F by dsimp [F]; ring]
  have hD := Nat.lt_mul_div_succ (2^n) hF
  rw [← hr] at hD
  have poly (k : ℕ) (hk : 256 ≤ k) : 320*128^5*(k+1)^6 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      calc
        _ ≤ 2*(320*128^5*(k+1)^6) := by
          obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
          ring_nf
          omega
        _ ≤ _ := by rw [pow_succ]; omega
  have hc : 160*(2*n+1)*F^5 ≤ 2^n := by
    apply le_trans _ (poly n hn)
    dsimp [F]
    calc
      _ ≤ 160*(2*(n+1))*(128*(n+1))^5 := by gcongr <;> omega
      _ = _ := by ring
  have h16 : (16:ℕ)^n = (2^n)^4 := by rw [← pow_mul, mul_comm n 4,pow_mul]; norm_num
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < F^5 by positivity)
  calc
    160*(2*n+1)*16^n*F^5 = (160*(2*n+1)*F^5)*(2^n)^4 := by rw [h16]; ring
    _ ≤ (2^n)*(2^n)^4 := Nat.mul_le_mul_right _ hc
    _ = (2^n)^5 := by ring
    _ ≤ (F*(r+1))^5 := Nat.pow_le_pow_left hD.le _
    _ = _ := by rw [mul_pow,mul_comm]

/-- At physical error 1/10 the actual maximum m has explicit exponential
upper and lower bounds. Budgets with s⁵ < m occur for at most a doubly
exponentially small fraction of time, uniformly over interval origins. -/
theorem gaussian_pauli_physical_maximum_and_fifth_power_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ m : ℕ, nearHilbertContinuousCircuitBudget N < m ∧ m ≤ 160*(2*N+1)*16^N ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
        ∃ S : ℝ, 0 ≤ S ∧ ∀ s : ℕ, s^5 < m → ∀ a T : ℝ, 0 ≤ T →
          (2:ℝ)^(2^N/1024) * volume.real ({t | HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+S := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hwin⟩ := gaussian_pauli_chain_early_cost_excursions_and_returns
  filter_upwards [gaussian_pauli_prefix_maximum_and_occupation_quantiles,hwin] with ω hm hw
  filter_upwards [hm,hw,eventually_ge_atTop 256] with k hk hocc hlarge
  let N := k+3
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  obtain ⟨m,hlow,hmax,_⟩ := hk (1/10) (by constructor <;> norm_num)
  obtain ⟨_,w,_,hw,hh⟩ := hmax.2
  obtain ⟨u,_,hu⟩ := hh 0
  obtain ⟨z,hz,C,hC,he⟩ := evolution_uniform_projective_gate_cap (by dsimp [N]; omega : 2 ≤ N) H u
  have hupper := (hu u ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC
  have hex : PhysicalExcursionAndReturns H := hocc.2
  obtain ⟨⟨S,hS,hmeasure⟩,_⟩ := hex
  refine ⟨m,hlow,hupper,hmax,S,hS,?_⟩
  intro s hs a T hT
  have hm' := hupper.trans (cap_le_excursion_power (by dsimp [N]; omega))
  have hr : s ≤ r := by
    by_contra! h
    exact (not_lt_of_ge ((Nat.pow_le_pow_left h 5))) (hs.trans_le hm')
  have hW : 0 ≤ W := by
    dsimp [W,translatedExcursionWidth]
    positivity
  have hsub : {t | HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t)} ⊆
      circuitWindowHits H.val r W := by
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,z,hz,C,hC.trans hr,he⟩
  have hf := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc a (a+T)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hpow : (2:ℝ)^(2^N/1024) ≤ ((r:ℝ)+1)^r := by
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  exact (mul_le_mul hpow hf ENNReal.toReal_nonneg (by positivity)).trans (hmeasure a T hT)

#print axioms gaussian_pauli_physical_maximum_and_fifth_power_occupation
end
end GaloisForLFunctions.HTGeometry
