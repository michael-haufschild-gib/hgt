import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliEarlyLateCircuitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ResolvedVisits

/-! # Mean spacing of successive low-complexity returns on one Gaussian chain -/
open MeasureTheory Filter Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Both spacing factors have logarithms of order the Hilbert dimension.
The lower bound uses the price of r gates and the r+1 possible labels per gate. -/
theorem circuit_return_spacing_factor_bounds {N : ℕ} (hN : 64 ≤ N) :
    let r := excursionGateBudget N
    2^(2^N/1024) ≤ (r+1)^r ∧ 100^(2^N-1) ≤ 2^(7*2^N) := by
  intro r
  let F := 128*(N+1)
  have hF : 0 < F := by dsimp [F]; positivity
  have hr : r = 2^N/F := by
    change (2^N/(64*(N+1)))/2 = _
    rw [Nat.div_div_eq_div_mul,show 64*(N+1)*2 = F by dsimp [F]; ring]
  have hpow (j : ℕ) (hj : 32 ≤ j) : 128*(2*j+2) ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih => rw [pow_succ]; omega
  have hhalf : F ≤ 2^(N/2) := (show 128*(N+1) ≤ 128*(2*(N/2)+2) by omega).trans (hpow _ (by omega))
  have hroot : 2^(N/2) ≤ r := by
    rw [hr,Nat.le_div_iff_mul_le hF]
    calc
      _ ≤ 2^(N/2)*2^(N/2) := Nat.mul_le_mul_left _ hhalf
      _ = 2^((N/2)*2) := by rw [pow_mul,pow_two]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hrpos : 0 < r := (by positivity : 0 < (2:ℕ)^(N/2)).trans_le hroot
  have hD := Nat.lt_mul_div_succ (2^N) hF
  rw [← hr] at hD
  have hD' : 2^N ≤ ((N/2)*r)*1024 := by
    calc
      _ ≤ F*(r+1) := hD.le
      _ ≤ F*(2*r) := Nat.mul_le_mul_left _ (by omega)
      _ = (2*F)*r := by ring
      _ ≤ (1024*(N/2))*r := Nat.mul_le_mul_right _ (by dsimp [F]; omega)
      _ = _ := by ring
  have hcount : 2^N/1024 ≤ (N/2)*r := (Nat.div_le_div_right hD').trans_eq (Nat.mul_div_cancel _ (by decide : 0 < 1024))
  constructor
  · calc
      _ ≤ 2^((N/2)*r) := Nat.pow_le_pow_right (by decide) hcount
      _ = (2^(N/2))^r := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left (hroot.trans (Nat.le_succ _)) _
  · calc
      _ ≤ 100^(2^N) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      _ ≤ (2^7)^(2^N) := Nat.pow_le_pow_left (by decide : 100 ≤ 2^7) _
      _ = _ := (pow_mul _ _ _).symm

/-- For at least 64 sites the exponential circuit budget pays for a unit of
physical time even at the quadratic spectral speed cutoff. -/
private theorem unit_resolution_le_width (n : ℕ) (hn : 64 ≤ n) {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ (n:ℝ)^2) :
    1 ≤ translatedExcursionWidth n v := by
  have grow (k : ℕ) (hk : 64 ≤ k) : 8192*(k+1)^3 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      calc
        _ ≤ 2*(8192*(k+1)^3) := by obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk; ring_nf; omega
        _ ≤ _ := by rw [pow_succ 2 k]; omega
  let r := excursionGateBudget n
  have hr : 64*(n+1)^2 ≤ r := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(n+1))).mpr
    exact (show 64*(n+1)^2*2*(64*(n+1))=8192*(n+1)^3 by ring).le.trans (grow n hn)
  have hpos : 1 ≤ r := (show 1 ≤ 64*(n+1)^2 from Nat.one_le_iff_ne_zero.mpr (by positivity)).trans hr
  have hpow : r+1 ≤ (r+1)^r := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < r+1) hpos
  have hc : 64*(n+1)^2 ≤ (r+1)^r-1 := by omega
  have hR : 64*((n:ℝ)+1)^2 ≤ (((r+1)^r-1:ℕ):ℝ) := by exact_mod_cast hc
  change 1 ≤ _*(1/(40*(v+1)))
  rw [mul_one_div,le_div_iff₀ (by positivity),one_mul]
  linarith only [hv',hR,Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ)]

private theorem gaussian_path_eventual_unit_excursion_width :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      1 ≤ translatedExcursionWidth (k+3) ‖pathHamiltonian (pathPauliDisorderShell ω (k+1))‖ := by
  obtain ⟨_,b,_,_,hm⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hm] with ω hω
  obtain ⟨m,hm⟩ := exists_nat_gt (12+b)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,eventually_ge_atTop m,eventually_ge_atTop 64] with k hmass hk hlarge
  let N := k+3
  let u := pathPauliDisorderShell ω (k+1)
  have hnorm : ‖pathHamiltonian u‖ ≤ ∑ l, |u l| := by
    rw [pathHamiltonian_eq_sum]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one])
  have hN : 12+b ≤ (N:ℝ) := hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  apply unit_resolution_le_width N (by dsimp [N]; omega) (norm_nonneg _)
  exact hnorm.trans ((path_pauli_coefficient_mass_le u b hmass.2).trans (by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg N)))

/-- On each sufficiently long prefix, choose any budget through half the
exponential threshold. Record the first actual hit at least h time units
after each previous one. Its nth arrival has two-sided linear bounds in n
with doubly exponential spacing factors, for every resolution up to W,
including one physical time unit. -/
theorem gaussian_pauli_mean_first_return_spacing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let r := excursionGateBudget N
      let W := translatedExcursionWidth N ‖H.val‖
      1 ≤ W ∧ ∃ S : ℝ, 0 ≤ S ∧ ∀ s ≤ r, ∀ h : ℝ, 0 < h → h ≤ W → ∀ a : ℝ, 0 ≤ a →
        ∃ t : ℕ → ℝ, t 0 = a ∧
          (∀ j, IsLeast {v | t j+h ≤ v ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v)} (t (j+1))) ∧
          ∀ j : ℕ, ((r+1:ℝ)^r)*(j*h) ≤ t j-a+S ∧ t j ≤ (100:ℝ)^(2^N-1)*(a+j*h) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hw⟩ := gaussian_pauli_chain_early_cost_excursions_and_returns
  filter_upwards [hw,gaussian_path_eventual_unit_excursion_width] with ω hω hwide
  filter_upwards [hω,hwide] with k hk hW
  let N := k+3
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  let e : (Fin N → Bool) ≃ Fin ((2^N-1)+1) := (qubitConfigFin N).trans (finCongr (by
    have h : 0 < (2:ℕ)^N := by positivity
    omega))
  have hex : PhysicalExcursionAndReturns H := hk.2
  obtain ⟨⟨S,hS,hocc⟩,_⟩ := hex
  refine ⟨hW,S,hS,?_⟩
  intro s hs h hh hwidth a ha
  let A := {v | HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v)}
  have least (a : ℝ) : ∃ v, IsLeast {u | a+h ≤ u ∧ u ∈ A} v := by
    obtain ⟨v,hv,he,hfirst⟩ := projective_first_circuit_visit_deadline e H (a+h) s
    refine ⟨v,⟨hv.1,he⟩,?_⟩
    rintro w ⟨hw,c,hc,C,hC,herr⟩
    by_contra! h
    exact (not_lt_of_ge herr) (hfirst w ⟨hw,h⟩ c hc C hC)
  choose hit hnext using least
  let t (i : ℕ) : ℝ := Nat.rec a (fun _ v => hit v) i
  have hfirst (i) : IsLeast {u | t i+h ≤ u ∧ u ∈ A} (t (i+1)) := hnext (t i)
  refine ⟨t,rfl,hfirst,?_⟩
  intro j
  have ht : a ≤ t j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (ih.trans (le_add_of_nonneg_right hh.le)).trans (hfirst j).1.1
  obtain ⟨hcover,hpack⟩ := resolved_visit_occupation_bounds A t a h W hh hwidth rfl hfirst j
  have hfinite {B : Set ℝ} : volume (B ∩ Icc a (t j)) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hsub : {u | ∃ v ∈ Icc u (u+W), v ∈ A} ⊆ circuitWindowHits H.val r W := by
    rintro u ⟨v,hv,c,hc,C,hC,he⟩
    exact ⟨v,hv,c,hc,C,hC.trans hs,he⟩
  have h0 : {v | HasProjectiveCircuitApproximation N (1/10:ℝ) 0 (unitaryEvolution H.val v)} ⊆ A := by
    rintro v ⟨c,hc,C,hC,he⟩; exact ⟨c,hc,C,hC.trans (Nat.zero_le s),he⟩
  have hL := hpack.trans (measureReal_mono (inter_subset_inter_left _ hsub) hfinite)
  let P := Icc 0 a ∪ (A ∩ Icc a (t j))
  have hbefore : {v | HasProjectiveCircuitApproximation N (1/10:ℝ) 0 (unitaryEvolution H.val v)} ∩ Icc 0 (t j) ⊆ P := by
    rintro v ⟨hv,hv0,hvj⟩
    exact (le_total v a).elim (fun he => Or.inl ⟨hv0,he⟩) (fun he => Or.inr ⟨h0 hv,he,hvj⟩)
  have hP : P ⊆ Icc 0 (t j) := union_subset (Icc_subset_Icc_right ht) (fun _ hx => ⟨ha.trans hx.2.1,hx.2.2⟩)
  have hU : volume.real P ≤ a+j*h := by
    apply (measureReal_union_le _ _).trans
    rw [Real.volume_real_Icc_of_le ha,sub_zero]
    exact add_le_add le_rfl hcover
  have hv := (measureReal_mono hbefore (measure_ne_top_of_subset hP measure_Icc_lt_top.ne)).trans hU
  refine ⟨(mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (r+1:ℝ)^r)).trans ?_,
    (zero_gate_prefix_occupation H (t j) (ha.trans ht)).trans (mul_le_mul_of_nonneg_left hv (by positivity))⟩
  simpa only [add_sub_cancel] using hocc a (t j-a) (sub_nonneg.mpr ht)

#print axioms gaussian_pauli_mean_first_return_spacing

/-- After any nonnegative starting time, the lower and upper asymptotic
mean spacings per resolution unit lie between 2^(D/1024 rounded down in
the exponent) and 2^(7D), where D is the Hilbert-space dimension. -/
theorem gaussian_pauli_double_exponential_mean_spacing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let r := excursionGateBudget N
      ∀ s ≤ r, ∀ a : ℝ, 0 ≤ a → ∃ t : ℕ → ℝ, t 0 = a ∧
        (∀ j, IsLeast {v | t j+1 ≤ v ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v)} (t (j+1))) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
          (2:ℝ)^(D/1024)-ε ≤ (t j-a)/j ∧ (t j-a)/j ≤ (2:ℝ)^(7*D)+ε := by
  filter_upwards [gaussian_pauli_mean_first_return_spacing] with ω hω
  filter_upwards [hω,eventually_ge_atTop 64] with k hk hbig
  let N := k+3
  let D : ℕ := 2^N
  let r := excursionGateBudget N
  let Q := (100:ℝ)^(D-1)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨hwidth,S,hS,hcases⟩ := hk
  obtain ⟨hL,hU⟩ := circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)
  have hL' : (2:ℝ)^(D/1024) ≤ ((r:ℝ)+1)^r := by exact_mod_cast hL
  have hU' : Q ≤ (2:ℝ)^(7*D) := by
    dsimp only [Q,D]
    exact_mod_cast hU
  intro _ _ _ _ s hs a ha
  obtain ⟨t,ht,hh,hbound⟩ := hcases s hs 1 zero_lt_one hwidth a ha
  refine ⟨t,ht,hh,?_⟩
  intro ε hε
  obtain ⟨b,hb⟩ := exists_nat_gt ((S+Q*a)/ε)
  filter_upwards [eventually_ge_atTop (b+1)] with j hj
  have hjpos : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hb' : (b:ℝ) ≤ j := by exact_mod_cast (show b ≤ j by omega)
  have hslack : S+Q*a ≤ ε*(j:ℝ) := by
    have h := (div_lt_iff₀ hε).mp hb
    linarith only [h,mul_le_mul_of_nonneg_right hb' hε.le]
  have hbound' : ((r:ℝ)+1)^r*j ≤ t j-a+S ∧ t j ≤ Q*(a+j) := by
    simpa only [mul_one] using hbound j
  refine ⟨(le_div_iff₀ hjpos).mpr ?_,(div_le_iff₀ hjpos).mpr ?_⟩
  · linarith only [mul_le_mul_of_nonneg_right hL' hjpos.le,hbound'.1,hslack,mul_nonneg hQ ha]
  · linarith only [mul_le_mul_of_nonneg_right hU' hjpos.le,hbound'.2,hslack,hS,ha]

#print axioms gaussian_pauli_double_exponential_mean_spacing
end
end GaloisForLFunctions.HTGeometry
