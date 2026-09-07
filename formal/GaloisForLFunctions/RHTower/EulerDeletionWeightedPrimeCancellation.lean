import GaloisForLFunctions.RHTower.EulerDeletionPeriodAveragingObstruction

/-!
# Large prime packets and actual weighted Möbius cancellation

The upper-half prime generators reinforce each other in the genuine carrier.
The remaining literal Möbius channels cancel their growing packet in relative norm.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionPrimePacket
open DeletionPeriodGrowth

/-- The positive upper-half prime contribution to the actual Möbius carrier. -/
def packet (N : ℕ) : BDCarrier := ∑ p ∈ upperPrimes N, bdGen (1 / (p : ℝ))

/-- The exact complementary source vector. -/
def remainder (N : ℕ) : BDCarrier := bdMobiusModularApproximantVec N - packet N

/-- Deleting precisely the packet's coefficients gives the complementary vector. -/
theorem remainder_eq_remaining_sum (N : ℕ) :
    remainder N = ∑ m ∈ (Finset.Icc 1 N) \ upperPrimes N,
      (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ)) • bdGen (1 / (m : ℝ)) := by
  have hp : (∑ m ∈ upperPrimes N,
      (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ)) • bdGen (1 / (m : ℝ))) = packet N := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [moebius_apply_prime (Finset.mem_filter.mp hp).2.1]
  have hsub : upperPrimes N ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hs := Finset.sum_sdiff hsub (f := fun m =>
      (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ)) • bdGen (1 / (m : ℝ)))
  rw [hp] at hs
  rw [remainder, bdMobiusModularApproximantVec_eq_generatorCombination,
    bdMobiusGeneratorCombination, ← hs, add_sub_cancel_right]

/-- The initial common residue segment gives a positive lower bound on every Gram entry. -/
theorem gram_lower_of_common_head {m n K : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hKm : K < m) (hKn : K < n) :
    (K : ℝ) / (2*(m : ℝ)*(n : ℝ)) ≤ bdGram (1/(m : ℝ)) (1/(n : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let g (j : ℕ) : ℝ := (((j+1)%m : ℕ) : ℝ)*(((j+1)%n : ℕ) : ℝ) /
    ((m : ℝ)*(n : ℝ)*((j : ℝ)+1)*((j : ℝ)+2))
  have hhead (j : ℕ) (hj : j ∈ Finset.range K) : 1/(2*(m : ℝ)*(n : ℝ)) ≤ g j := by
    have hjK := Finset.mem_range.mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    dsimp [g]
    rw [Nat.mod_eq_of_lt (by omega : j+1 < m), Nat.mod_eq_of_lt (by omega : j+1 < n)]
    push_cast
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hm0.le hn0.le) (show 0 ≤ (j : ℝ)*((j : ℝ)+1) by positivity)]
  calc (K : ℝ)/(2*(m : ℝ)*(n : ℝ)) = ∑ j ∈ Finset.range K, 1/(2*(m : ℝ)*(n : ℝ)) := by
         simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
       _ ≤ ∑ j ∈ Finset.range K, g j := Finset.sum_le_sum hhead
       _ ≤ _ := sum_le_hasSum (Finset.range K) (fun j _ => by dsimp [g]; positivity)
         (hasSum_bdGram_discrete hm hn)

/-- All prime-packet cross terms reinforce the common initial segment. -/
theorem packet_norm_sq_lower (N : ℕ) :
    ((N/2 : ℕ) : ℝ)/2 * (∑ p ∈ upperPrimes N, 1/(p : ℝ))^2 ≤ ‖packet N‖^2 := by
  have hgram := bdGram_quadraticForm_eq_norm_sq (upperPrimes N)
    (fun p => 1/(p : ℝ)) (fun _ => (1 : ℝ))
  simp only [one_mul, Complex.ofReal_one, one_smul] at hgram
  rw [packet, ← hgram]
  calc _ = ∑ p ∈ upperPrimes N, ∑ q ∈ upperPrimes N,
          ((N/2 : ℕ) : ℝ)/(2*(p : ℝ)*(q : ℝ)) := by
         simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro p hp
         apply Finset.sum_congr rfl
         intro q hq
         ring
       _ ≤ _ := by
         apply Finset.sum_le_sum
         intro p hp
         apply Finset.sum_le_sum
         intro q hq
         obtain ⟨hpI,hpPrime,hpN⟩ := Finset.mem_filter.mp hp
         obtain ⟨hqI,hqPrime,hqN⟩ := Finset.mem_filter.mp hq
         exact gram_lower_of_common_head (Finset.mem_Icc.mp hpI).1 (Finset.mem_Icc.mp hqI).1
           ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
           ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))

private theorem upperPrime_card_eq_shell (N : ℕ) :
    (upperPrimes N).card = primeShellCard ((N : ℝ)/2) (N : ℝ) := by
  unfold primeShellCard
  rw [Nat.floor_natCast]
  apply congrArg Finset.card
  ext p
  simp only [upperPrimes, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp1,hpN⟩,hp,hhalf⟩
    refine ⟨⟨?_,hpN⟩,hp⟩
    rw [Nat.floor_lt (by positivity)]
    have h : (N : ℝ) < 2*(p : ℝ) := by exact_mod_cast hhalf
    linarith
  · rintro ⟨⟨hfloor,hpN⟩,hp⟩
    have hhalf : (N : ℝ)/2 < (p : ℝ) := (Nat.floor_lt (by positivity)).mp hfloor
    refine ⟨⟨hp.pos,hpN⟩,hp,?_⟩
    exact_mod_cast (show (N : ℝ) < 2*(p : ℝ) by linarith)

private theorem rpow_three_quarters_eventually_le :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^((3 : ℝ)/4) ≤ (N : ℝ)/4 := by
  have hlim := (tendsto_rpow_neg_atTop (y := (1 : ℝ)/4) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1/4 by norm_num))
  filter_upwards [he,eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hp : (N : ℝ)^((3 : ℝ)/4) = (N : ℝ)*(N : ℝ)^(-((1 : ℝ)/4)) := by
    calc _ = (N : ℝ)^((1 : ℝ)+-((1 : ℝ)/4)) := by congr 1; norm_num
         _ = _ := by rw [Real.rpow_add hN0,Real.rpow_one]
  rw [hp]
  change (N : ℝ)^(-((1 : ℝ)/4)) < 1/4 at hN
  calc _ ≤ (N : ℝ)*(1/4) := mul_le_mul_of_nonneg_left hN.le hN0.le
       _ = _ := by ring

/-- Unconditional prime-shell count at the actual coefficient cutoff. -/
theorem upperPrime_card_eventually_lower :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)/(32768*Real.log (N : ℝ)) ≤ ((upperPrimes N).card : ℝ) := by
  obtain ⟨X,hX,hwin⟩ := Sieve.exists_theta_window_lower (α := (3 : ℝ)/4) (by norm_num) (by norm_num)
  have hx := ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const
    (show (0 : ℝ) < 2 by norm_num)).eventually_ge_atTop X
  filter_upwards [hx,rpow_three_quarters_eventually_le,eventually_ge_atTop 4]
    with N hNX hpow hN4
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hw := hwin ((N : ℝ)/2) ((N : ℝ)/2) hNX (by positivity)
  rw [show (N : ℝ)/2+(N : ℝ)/2=(N : ℝ) by ring] at hw
  have hmass : (N : ℝ)/32768 ≤ Chebyshev.theta (N : ℝ)-Chebyshev.theta ((N : ℝ)/2) := by
    linarith
  have hcount := (primeShellCard_bounds (a := (N : ℝ)/2) (b := (N : ℝ))
    (by linarith) (by linarith)).1
  have hc : (N : ℝ)/(32768*Real.log (N : ℝ)) ≤ ((upperPrimes N).card : ℝ) := by
    calc _ = ((N : ℝ)/32768)/Real.log (N : ℝ) := by ring
         _ ≤ (Chebyshev.theta (N : ℝ)-Chebyshev.theta ((N : ℝ)/2))/Real.log (N : ℝ) :=
           div_le_div_of_nonneg_right hmass hlog.le
         _ ≤ (primeShellCard ((N : ℝ)/2) (N : ℝ) : ℝ) := hcount
         _ = _ := by rw [upperPrime_card_eq_shell]
  exact hc

/-- The genuine weighted packet has at least N divided by a fixed squared-log scale. -/
theorem packet_norm_sq_eventually_lower :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)/(8*(32768 : ℝ)^2*Real.log (N : ℝ)^2) ≤ ‖packet N‖^2 := by
  filter_upwards [upperPrime_card_eventually_lower,eventually_ge_atTop 4] with N hc hN4
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hrecip : ((upperPrimes N).card : ℝ)/(N : ℝ) ≤ ∑ p ∈ upperPrimes N, 1/(p : ℝ) := by
    calc _ = ∑ p ∈ upperPrimes N, 1/(N : ℝ) := by simp; ring
         _ ≤ _ := by
           apply Finset.sum_le_sum
           intro p hp
           have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
           exact div_le_div_of_nonneg_left (by norm_num)
             (by exact_mod_cast hpI.1) (by exact_mod_cast hpI.2)
  have hh : 1/(32768*Real.log (N : ℝ)) ≤ ∑ p ∈ upperPrimes N, 1/(p : ℝ) := by
    calc _ = ((N : ℝ)/(32768*Real.log (N : ℝ)))/(N : ℝ) := by field_simp
         _ ≤ ((upperPrimes N).card : ℝ)/(N : ℝ) := div_le_div_of_nonneg_right hc hN0.le
         _ ≤ _ := hrecip
  have hK : (N : ℝ)/8 ≤ ((N/2 : ℕ) : ℝ)/2 := by
    have hn : N ≤ 4*(N/2) := by omega
    have hr : (N : ℝ) ≤ 4*((N/2 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hs : (1/(32768*Real.log (N : ℝ)))^2 ≤ (∑ p ∈ upperPrimes N, 1/(p : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) hh 2
  calc _ = (N : ℝ)/8*(1/(32768*Real.log (N : ℝ)))^2 := by ring
       _ ≤ ((N/2 : ℕ) : ℝ)/2*(∑ p ∈ upperPrimes N, 1/(p : ℝ))^2 :=
         mul_le_mul hK hs (sq_nonneg _) (by positivity)
       _ ≤ _ := packet_norm_sq_lower N

/-- The packet is eventually nonzero, so its normalization carries no hidden zero convention. -/
theorem packet_norm_eventually_pos : ∀ᶠ N : ℕ in atTop, 0 < ‖packet N‖ := by
  filter_upwards [packet_norm_sq_eventually_lower,eventually_ge_atTop 2] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hl : 0 < (N : ℝ)/(8*(32768 : ℝ)^2*Real.log (N : ℝ)^2) := by positivity
  nlinarith [norm_nonneg (packet N)]

/-- Every fixed logarithmic order of relative squared cancellation holds for the actual source. -/
theorem source_relative_energy_log_pow_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ)^q / ‖packet N‖^2)
      atTop (𝓝 0) := by
  have hlim := (DeletionMobiusGlobal.modular_norm_log_pow_div_tendsto_zero (q+2)).const_mul
    (8*(32768 : ℝ)^2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (Real.log_pos hN1).le q)) (sq_nonneg _)
  · filter_upwards [packet_norm_sq_eventually_lower,packet_norm_eventually_pos,eventually_ge_atTop 2]
      with N hN hp hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hmul := (div_le_iff₀ (show 0 < 8*(32768 : ℝ)^2*Real.log (N : ℝ)^2 by positivity)).mp hN
    calc _ ≤ ((8*(32768 : ℝ)^2)*‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ)^(q+2))/(N : ℝ) := by
           apply (div_le_div_iff₀ (sq_pos_of_pos hp) hN0).mpr
           rw [pow_add]
           nlinarith [mul_le_mul_of_nonneg_left hmul
             (show 0 ≤ ‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ)^q by positivity)]
         _ = _ := by ring

/-- The full residual is negligible relative to the growing positive packet. -/
theorem source_relative_norm_tendsto_zero :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖/‖packet N‖) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp (source_relative_energy_log_pow_tendsto_zero 0)
  simpa only [Function.comp_def,pow_zero,mul_one,Real.sqrt_zero,
    Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)] using h

/-- The complementary literal coefficients have asymptotically the same norm as the packet. -/
theorem remainder_relative_norm_tendsto_one :
    Tendsto (fun N : ℕ => ‖remainder N‖/‖packet N‖) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) _ source_relative_norm_tendsto_zero
  filter_upwards [packet_norm_eventually_pos] with N hp
  have h := abs_norm_sub_norm_le (remainder N) (-packet N)
  have he : remainder N - -packet N = bdMobiusModularApproximantVec N := by
    simp [remainder]
  rw [norm_neg,he] at h
  rw [Real.norm_eq_abs, show ‖remainder N‖/‖packet N‖-1 =
    (‖remainder N‖-‖packet N‖)/‖packet N‖ by field_simp]
  rw [abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right h hp.le

/-- Actual weighted cross interference cancels one full prime-packet energy asymptotically. -/
theorem packet_remainder_inner_div_energy_tendsto_neg_one :
    Tendsto (fun N : ℕ => (inner ℂ (packet N) (remainder N)).re/‖packet N‖^2) atTop (𝓝 (-1)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) _ source_relative_norm_tendsto_zero
  filter_upwards [packet_norm_eventually_pos] with N hp
  have he : (inner ℂ (packet N) (remainder N)).re =
      (inner ℂ (packet N) (bdMobiusModularApproximantVec N)).re - ‖packet N‖^2 := by
    rw [remainder,inner_sub_right,Complex.sub_re]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (packet N)
  have hbound := (Complex.abs_re_le_norm (inner ℂ (packet N) (bdMobiusModularApproximantVec N))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (packet N) (bdMobiusModularApproximantVec N))
  rw [Real.norm_eq_abs,he,show ((inner ℂ (packet N) (bdMobiusModularApproximantVec N)).re -
      ‖packet N‖^2)/‖packet N‖^2 - -1 =
      (inner ℂ (packet N) (bdMobiusModularApproximantVec N)).re/‖packet N‖^2 by field_simp; ring]
  rw [abs_div,abs_of_pos (sq_pos_of_pos hp)]
  calc _ ≤ (‖packet N‖*‖bdMobiusModularApproximantVec N‖)/‖packet N‖^2 :=
         div_le_div_of_nonneg_right hbound (sq_nonneg _)
       _ = _ := by field_simp

/-- The actual packet and its complement approach opposite directions in the weighted carrier. -/
theorem packet_remainder_normalized_inner_tendsto_neg_one :
    Tendsto (fun N : ℕ => (inner ℂ (packet N) (remainder N)).re/(‖packet N‖*‖remainder N‖))
      atTop (𝓝 (-1)) := by
  have h := packet_remainder_inner_div_energy_tendsto_neg_one.div
    remainder_relative_norm_tendsto_one (by norm_num)
  simp only [div_one] at h
  have hr := remainder_relative_norm_tendsto_one.eventually
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  apply h.congr'
  filter_upwards [packet_norm_eventually_pos,hr] with N hp hR
  have hR0 : ‖remainder N‖ ≠ 0 := by intro hz; simp [hz] at hR
  dsimp
  field_simp

end RHTower.DeletionPrimePacket
end
