import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.TheSquareRootFloorOfEveryIntegerAlphabet

/-!
# Endpoint rate at an actual zero

The log-free peak bound turns the producer inequality at a zero into a
uniform lower bound of order K^(Re ρ - 1). A vanishing normalized rate
along any single family excludes zeros on the endpoint line as well as
to its right. No uniformity in the gaps between its alphabet sizes is needed.
-/

open Filter Topology
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

private theorem peak_constant : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B → AlphabetLE c K →
      IsProducer.peakRatio c m ≤ C*(K:ℝ)*rate c m B := by
  obtain ⟨η,hη,H⟩ := exists_log_free_half_floor
  refine ⟨272+4/η,by have := div_pos (by norm_num : (0:ℝ)<4) hη; linarith,
    fun K c m B hK hP hA => ?_⟩
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hroot := Real.one_le_sqrt.mpr hk
  have hp := lt_of_lt_of_le zero_lt_one hroot
  have he := (div_le_iff₀ hp).mp (H _ _ _ _ hK hP hA)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) K)
  have hlt : Real.sqrt K ≤ K := by
    nlinarith only [hs,mul_nonneg (sub_nonneg.mpr hroot) hp.le]
  have hKε : η ≤ (K:ℝ)*rate c m B := he.trans (by
    rw [mul_comm (K:ℝ)]
    exact mul_le_mul_of_nonneg_left hlt hP.rate_pos.le)
  have hc : 4 ≤ (4/η)*((K:ℝ)*rate c m B) := by
    calc (4:ℝ) = (4/η)*η := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left hKε (by positivity)
  have hpeak := peak_le_sinc_excess hP hK hA
  have ht := mul_le_mul_of_nonneg_left hP.excess_le (by positivity : 0 ≤ 272*(K:ℝ))
  change (peak c : ℝ)/m ≤ _
  rw [div_le_iff₀ hP.m_pos]
  have hcm := mul_le_mul_of_nonneg_right hc hP.m_pos.le
  linarith only [hpeak,ht,hcm]

/-- Every zero in the right half of the critical strip bounds the rate at its own
abscissa for each producer, including sparse choices of the alphabet size. -/
theorem exists_actual_zero_rate_floor :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B → AlphabetLE c K →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1/2 ≤ ρ.re → ρ.re ≤ 1 →
        η ≤ (1+‖ρ‖)*(K:ℝ)^(1-ρ.re)*rate c m B := by
  obtain ⟨C,hC,H⟩ := peak_constant
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨1/(24*C),by positivity,fun K c m B hK hP hA ρ hρ hβ hβ' => ?_⟩
  let ε := rate c m B
  let x := IsProducer.peakRatio c m
  have hε : 0 < ε := hP.rate_pos
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hx : 0 ≤ x := zero_le_one.trans hP.one_le_peakRatio
  have hpow : 1 ≤ (K:ℝ)^(1-ρ.re) := Real.one_le_rpow hk (sub_nonneg.mpr hβ')
  by_cases hsmall : ε ≤ 1
  · have hz := hP.zero_law hsmall hρ hβ hβ'
    have he := Real.rpow_le_rpow hx (H K c m B hK hP hA) (sub_nonneg.mpr hβ')
    have hp : x^(1-ρ.re)*ε^ρ.re ≤ C*(K:ℝ)^(1-ρ.re)*ε := by
      calc _ ≤ (C*(K:ℝ)*ε)^(1-ρ.re)*ε^ρ.re :=
             mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hε.le _)
           _ = C^(1-ρ.re)*(K:ℝ)^(1-ρ.re)*ε := by
             rw [Real.mul_rpow (mul_nonneg hCp.le (Nat.cast_nonneg _)) hε.le,
               Real.mul_rpow hCp.le (Nat.cast_nonneg _), mul_assoc (_*_), ← Real.rpow_add hε,
               sub_add_cancel, Real.rpow_one]
           _ ≤ _ := by
             have h := Real.rpow_le_rpow_of_exponent_le hC (by linarith only [hβ] : 1-ρ.re ≤ 1)
             rw [Real.rpow_one] at h
             exact mul_le_mul_of_nonneg_right
               (mul_le_mul_of_nonneg_right h (zero_le_one.trans hpow)) hε.le
    have hmain := hz.trans (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 24*‖ρ‖))
    rw [div_le_iff₀ (by positivity)]
    change 1 ≤ (1+‖ρ‖)*(K:ℝ)^(1-ρ.re)*ε*(24*C)
    nlinarith only [hmain,mul_nonneg (mul_nonneg hCp.le (zero_le_one.trans hpow)) hε.le]
  · have hlo : 1/(24*C) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hC])
    exact hlo.trans (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith only [norm_nonneg ρ]) hpow) (le_of_not_ge hsmall))

/-- A vanishing power-normalized rate excludes the closed half-strip with that boundary. -/
theorem zeta_ne_zero_on_endpoint_of_vanishing_rate
    (K m B : ℕ → ℕ) (c : ℕ → ℕ →₀ ℤ) (a : ℝ)
    (h : ∀ n, 1 ≤ K n ∧ IsProducer (c n) (m n) (B n) ∧ AlphabetLE (c n) (K n))
    (hlim : Tendsto (fun n => (K n : ℝ)^a * rate (c n) (m n) (B n)) atTop (𝓝 0)) :
    ∀ ρ : ℂ, 1/2 ≤ ρ.re → 1-a ≤ ρ.re → riemannZeta ρ ≠ 0 := by
  intro ρ hβ ha hρ
  by_cases hβ' : ρ.re ≤ 1
  · obtain ⟨η,hη,H⟩ := exists_actual_zero_rate_floor
    have ht : Tendsto (fun n => (1+‖ρ‖)*((K n : ℝ)^a * rate (c n) (m n) (B n))) atTop (𝓝 0) := by
      simpa using hlim.const_mul (1+‖ρ‖)
    have hh := ge_of_tendsto' ht (fun n => by
      have hn := h n
      have hp := H (K n) (c n) (m n) (B n) hn.1 hn.2.1 hn.2.2 ρ hρ hβ hβ'
      have hK : (1:ℝ) ≤ K n := by exact_mod_cast hn.1
      have hr := Real.rpow_le_rpow_of_exponent_le hK (by linarith only [ha] : 1-ρ.re ≤ a)
      rw [←mul_assoc]
      exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) hn.2.1.rate_pos.le))
    exact hη.not_ge hh
  · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_ge hβ') hρ

/-- At a zero to the right of the critical line, even the optimal square-root-normalized
rate diverges with the alphabet. The lower bound is uniform over all rows at each size. -/
theorem normalized_rates_escape_at_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ : 1/2 < ρ.re) (U : ℝ) :
    ∀ᶠ K : ℕ in atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B → AlphabetLE c K →
      U < Real.sqrt K * rate c m B := by
  have hβ' : ρ.re ≤ 1 := le_of_not_gt (fun h => riemannZeta_ne_zero_of_one_le_re h.le hρ)
  obtain ⟨η,hη,H⟩ := exists_actual_zero_rate_floor
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hβ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hn : 0 < 1+‖ρ‖ := by positivity
  filter_upwards [eventually_ge_atTop 1, ht.eventually_gt_atTop (U*(1+‖ρ‖)/η)] with K hK hcut
  intro c m B hP hA
  have hk : 0 < (K:ℝ) := Nat.cast_pos.mpr hK
  have hf := H K c m B hK hP hA ρ hρ hβ.le hβ'
  change U*(1+‖ρ‖)/η < (K:ℝ)^(ρ.re-1/2) at hcut
  rw [div_lt_iff₀ hη] at hcut
  have hh := mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hk.le (ρ.re-1/2))
  have he : (K:ℝ)^(ρ.re-1/2) * ((1+‖ρ‖)*(K:ℝ)^(1-ρ.re)*rate c m B) =
      (Real.sqrt K*rate c m B)*(1+‖ρ‖) := by
    calc _ = ((K:ℝ)^(ρ.re-1/2)*(K:ℝ)^(1-ρ.re)*rate c m B)*(1+‖ρ‖) := by ring
         _ = _ := by rw [← Real.rpow_add hk,show (ρ.re-1/2)+(1-ρ.re) = 1/2 by ring,Real.sqrt_eq_rpow]
  exact (lt_of_mul_lt_mul_right (hcut.trans_le (hh.trans_eq he)) hn.le)

/-- A bounded square-root-normalized rate on arbitrarily sparse alphabet sizes implies RH. -/
theorem riemannHypothesis_of_frequent_half_rate
    (h : ∃ U : ℝ, ∃ᶠ K : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B ∧ AlphabetLE c K ∧ Real.sqrt K*rate c m B ≤ U) : RiemannHypothesis := by
  obtain ⟨U,hU⟩ := h
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro ρ hβ _ hρ
  obtain ⟨K,⟨c,m,B,hP,hA,hbound⟩,hall⟩ :=
    (hU.and_eventually (normalized_rates_escape_at_offline_zero hρ hβ U)).exists
  exact (hall c m B hP hA).not_ge hbound

/-- A certificate with rate times height below one requires a quadratic alphabet in the height. -/
theorem exists_quadratic_certificate_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ) (T : ℝ), 1 ≤ K → IsProducer c m B →
      AlphabetLE c K → 0 < T → rate c m B*T < 1 → C*T^2 < K := by
  obtain ⟨η,hη,H⟩ := exists_log_free_half_floor
  refine ⟨η^2,sq_pos_of_pos hη, fun K c m B T hk hP hA hT ht => ?_⟩
  have hK : 0 < Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have h := (mul_le_mul_of_nonneg_right (H _ _ _ _ hk hP hA) hT.le).trans_lt ht
  rw [div_mul_eq_mul_div,div_lt_one hK] at h
  have he := mul_self_lt_mul_self (mul_nonneg hη.le hT.le) h
  rw [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) K)] at he
  linarith only [he]

#print axioms exists_actual_zero_rate_floor
#print axioms zeta_ne_zero_on_endpoint_of_vanishing_rate
#print axioms normalized_rates_escape_at_offline_zero
#print axioms riemannHypothesis_of_frequent_half_rate
#print axioms exists_quadratic_certificate_cost

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
