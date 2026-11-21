import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.Itineraries

/-! # The price of a long run at physical gate error one tenth -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem itinerary_entropy (n s m : ℕ) (hs : s ≤ 2^n) :
    (((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/(1/40))^32)^s)^m ≤
      Real.exp ((36+128/(1/40))*((n:ℝ)+1)*((m*(s+1):ℕ)+1:ℝ)) := by
  let C : ℝ := 36+128/(1/40)
  have hh := net_envelope_le_exp n s (1/40) (by norm_num) hs
  apply (pow_le_pow_left₀ (by positivity) hh m).trans
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast
  have hc : 0 ≤ C*((n:ℝ)+1) := by dsimp [C]; positivity
  dsimp [C] at hc
  nlinarith only [hc]

/-- If m(s+1)=o(D/N), persisting at s gates for the first m multiples pays
the factor m to the power 1−D, between two explicit exponential factors.
The schedules and the observation origin may depend on the Gaussian draw. -/
theorem gaussian_physical_run_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s m : ℕ → ℕ,
      (∀ n, 0 < m n) → subcriticalBudget (fun n => m n*(s n+1)) →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let M := m N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          let f := volume.real (circuitRunSet H (s N) M (1/10) ∩ Icc a T)/(T-a)
          ((D:ℝ)/2)*((1/64:ℝ)/(M:ℝ))^(D-1) < f ∧ f < (1/4:ℝ)^D/(M:ℝ)^(D-1) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro s m hpos hsub
  have he := enlarged_arc_eventually_lt hsub (36+128/(1/40)) (1/8) (1/4) (by norm_num) (by norm_num)
  have hh := (tendsto_add_atTop_nat 3).eventually (he.and (budget_le_dimension_eventually hsub))
  filter_upwards [hh] with k hk
  intro N D M H a
  have hm : 0 < M := hpos N
  have hm' : 0 < (M:ℝ) := by exact_mod_cast hm
  have hs : s N ≤ D := (Nat.le_succ _).trans ((Nat.le_mul_of_pos_left _ hm).trans hk.2)
  have hx : 2*((1/10:ℝ)+1/40) ≤ zeroGateArcTolerance (1/8) :=
    (by norm_num : 2*((1/10:ℝ)+1/40) ≤ 3*(1/8)).trans (three_mul_le_arcTolerance (by norm_num) (by norm_num))
  have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hω k
  have hu := circuit_run_bound H hmax (s N) M hm (δ := 1/40) (by norm_num)
    (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num) hx a ((1/4:ℝ)^D/(M:ℝ)^(D-1)) (by
      simp only [zeroGateArcDensity,div_pow,←mul_div_assoc]
      apply (div_lt_div_iff_of_pos_right (pow_pos hm' _)).mpr
      rw [mul_assoc]
      have hcost := itinerary_entropy N (s N) M hs
      apply (mul_le_mul_of_nonneg_right hcost (by positivity)).trans_lt
      simpa only [Nat.cast_pow,Nat.cast_ofNat,D,N,M] using hk.1)
  let r : Icc (0:ℝ) (1/2) := ⟨(1/64:ℝ)/(M:ℝ),by positivity,
    (div_le_self (by norm_num) (by exact_mod_cast hm)).trans (by norm_num)⟩
  have hr : zeroGateArcTolerance (1/64) ≤ (1/10:ℝ) := by
    have hsin := Real.sin_le (show 0 ≤ Real.pi*(1/64)/2 by positivity)
    dsimp only [zeroGateArcTolerance]
    linarith only [hsin,Real.pi_lt_four]
  have hinc : zeroGateReturnSet H r ⊆ circuitRunSet H (s N) M (1/10) := by
    rw [show zeroGateReturnSet H r = runSet H (zeroGateArcTolerance (1/64)) M from
      (runSet_eq H (by norm_num) (by norm_num) M hm).symm]
    intro t ht i
    obtain ⟨c,hc,C,hC,herr⟩ := ht (i.val+1) i.isLt
    exact ⟨c,hc,C,hC.trans (Nat.zero_le _),by simpa only [Nat.cast_add_one] using herr.trans hr⟩
  have hd : (0:ℝ) < D := by dsimp [D]; positivity
  have hlow : ((D:ℝ)/2)*((1/64:ℝ)/(M:ℝ))^(D-1) < zeroGateArcDensity D r :=
    mul_lt_mul_of_pos_right (by linarith only [hd]) (pow_pos (div_pos (by norm_num) hm') _)
  have hl := (maximallyProjective_zeroGateOccupation_from_start H hmax r a).eventually_const_lt hlow
  filter_upwards [hu,hl,eventually_gt_atTop a] with T hhi hlo hT
  refine ⟨hlo.trans_le ?_,hhi⟩
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  exact measureReal_mono (inter_subset_inter_left _ hinc) (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

private theorem half_exponential_schedule (p : ℕ) :
    subcriticalBudget (fun n => (2^(n/2))*(n^p+1)) := by
  let a := Real.sqrt 2
  have ha2 : a^2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : 1 < a := by
    have h := Real.sqrt_nonneg 2
    dsimp [a] at *
    nlinarith only [h,ha2]
  have hl := (tendsto_pow_const_div_const_pow_of_one_lt (p+1) ha).const_mul (6:ℝ)
  rw [mul_zero] at hl
  unfold subcriticalBudget
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hpow : 1 ≤ (n:ℝ)^p := one_le_pow₀ h1
  have hhalf : (2:ℝ)^(n/2) ≤ a^n := by
    rw [←ha2,←pow_mul]
    exact pow_le_pow_right₀ ha.le (by omega)
  have hfull : (2:ℝ)^n = a^n*a^n := by rw [←mul_pow,←sq,ha2]
  have halfpos : 0 < a^n := pow_pos (zero_lt_one.trans ha) _
  have hnum : ((n:ℝ)+1)*((2:ℝ)^(n/2)*((n:ℝ)^p+1)+1) ≤ 6*(n:ℝ)^(p+1)*a^n := by
    have h2 : (2:ℝ)^(n/2)*((n:ℝ)^p+1)+1 ≤ a^n*((n:ℝ)^p+2) := by
      have hmain := mul_le_mul_of_nonneg_right hhalf (by positivity : 0 ≤ (n:ℝ)^p+1)
      have hh := one_le_pow₀ ha.le (n := n)
      nlinarith only [hmain,hh]
    have hpoly := mul_le_mul (by linarith only [h1] : (n:ℝ)+1 ≤ 2*n)
      (by linarith only [hpow] : (n:ℝ)^p+2 ≤ 3*n^p) (by positivity) (by positivity)
    calc
      _ ≤ ((n:ℝ)+1)*(a^n*((n:ℝ)^p+2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (((n:ℝ)+1)*((n:ℝ)^p+2))*a^n := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hpoly halfpos.le).trans_eq (by rw [pow_succ]; ring)
  push_cast
  rw [hfull]
  apply (div_le_iff₀ (mul_pos halfpos halfpos)).mpr
  exact hnum.trans_eq (by field_simp <;> ring)

/-- For any polynomial gate budget, requiring affordability for 2^⌊N/2⌋
harmonics has long-time fraction between two explicit multiples of
(2^⌊N/2⌋)^(1−D). Their logarithms differ by at most a constant times D. -/
theorem gaussian_polynomial_exponential_runs :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ p : ℕ, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let M := (2:ℕ)^(N/2)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        let f := volume.real (circuitRunSet H (N^p) M (1/10) ∩ Icc a T)/(T-a)
        ((D:ℝ)/2)*((1/64:ℝ)/(M:ℝ))^(D-1) < f ∧ f < (1/4:ℝ)^D/(M:ℝ)^(D-1) := by
  filter_upwards [gaussian_physical_run_rate] with ω hω
  exact fun p => hω _ _ (fun n => pow_pos (by decide : 0 < (2:ℕ)) (n/2)) (half_exponential_schedule p)

#print axioms gaussian_polynomial_exponential_runs
#print axioms gaussian_physical_run_rate
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
