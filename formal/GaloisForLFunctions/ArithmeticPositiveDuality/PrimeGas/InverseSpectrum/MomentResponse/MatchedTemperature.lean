import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Families

/-! # Calibrating the partition change with one occupation of the same heat wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Every constraint and output in this window is a value of the same relative partition function. -/
def thermalAmplitudeWindow (σ t D : ℝ) : Set ℝ :=
  {x | ∃ b ∈ physicalSpectra 1, ‖relativePartition b (σ:ℂ)‖ ≤ D ∧ ‖relativePartition b (⟨σ,t⟩:ℂ)‖ = x}

private theorem real_loss_norm (q : GibbsExponent) {r : ℕ} (b : SpectralBand r) :
    ‖relativePartition b (q.val:ℂ)‖ = momentLoss q b := by
  rw [relativePartition_real b q,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (momentLoss_nonneg q b)]

/-- Maximum clock response when the real partition change has at most one shell's Born scale. -/
def sameTemperatureResponse (σ t : ℝ) : ℝ := sSup (thermalAmplitudeWindow σ t (1/t^(2*σ)))

/-- The same-temperature response has exponent 1−2σ over the entire positive half-plane. -/
theorem same_temperature_bounds {σ t : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) :
    (highWindowFactor σ/5)*t^(1-2*σ) < sameTemperatureResponse σ t ∧
      sameTemperatureResponse σ t ≤ ((σ+1)/σ)*t^(1-2*σ) := by
  let q : GibbsExponent := ⟨σ,hs⟩
  have ht' := zero_lt_one.trans_le ht
  have hsq : t ≤ t^2 := (le_mul_of_one_le_right ht'.le ht).trans_eq (sq t).symm
  have he : t^(2*σ) = (t^2)^σ := by rw [Real.rpow_mul ht'.le,Real.rpow_two]
  have hD : (1/t^2)^σ = 1/t^(2*σ) := by rw [one_div (t^2),Real.inv_rpow (sq_nonneg _),he,one_div]
  have hscale : t/(t^2)^σ = t^(1-2*σ) := by rw [Real.rpow_sub ht',Real.rpow_one,he]
  obtain ⟨b,hphys,hL,hbudget⟩ := physical_moment_family_probe q hs ht hsq
  have hx : ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ∈ thermalAmplitudeWindow σ t (1/t^(2*σ)) :=
    ⟨b,hphys,(real_loss_norm q b).trans_le ((hbudget q le_rfl).trans_eq hD),rfl⟩
  have hu (x : ℝ) (hmem : x ∈ thermalAmplitudeWindow σ t (1/t^(2*σ))) : x ≤ ((σ+1)/σ)*t^(1-2*σ) := by
    obtain ⟨c,_,hcap,rfl⟩ := hmem
    change ‖relativePartition c (q.val:ℂ)‖ ≤ _ at hcap
    rw [real_loss_norm,← hD] at hcap
    simpa only [hscale] using own_moment_amplitude_cap hs ht hsq c hcap
  rw [hscale] at hL
  exact ⟨hL.trans_le (le_csSup ⟨_,hu⟩ hx),csSup_le ⟨_,hx⟩ hu⟩

theorem same_temperature_log_slope {σ : ℝ} (hs : 0 < σ) :
    Tendsto (fun t : ℝ => Real.log (sameTemperatureResponse σ t)/Real.log t) atTop (𝓝 (1-2*σ)) :=
  log_slope_of_power_bounds (div_pos (highWindowFactor_pos σ) (by norm_num : (0:ℝ)<5)) (div_pos (add_pos hs zero_lt_one) hs)
    (fun _ ht => ⟨(same_temperature_bounds hs ht).1.le,(same_temperature_bounds hs ht).2⟩)

theorem same_temperature_zero_iff_split {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => Real.log (sameTemperatureResponse s.re t)/Real.log t) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have he := tendsto_nhds_unique (same_temperature_log_slope hs) h
    linarith only [he]
  · intro h
    simpa only [show 1-2*s.re = 0 by rw [h]; norm_num] using same_temperature_log_slope hs

/-- At the clock height labelled by an occupation n, use its own Born weight as the tolerance. The response measures the full outgoing probability of that occupation. -/
theorem shell_calibrated_partition_response {s : ℂ} (hs : 0 < s.re) (n : ℕ+) :
    let A := thermalAmplitudeWindow s.re (n:ℕ) (‖heat s n‖^2)
    (highWindowFactor s.re/5)*shellMass s n < sSup A ∧ sSup A ≤ ((s.re+1)/s.re)*shellMass s n := by
  let t : ℝ := (n:ℕ)
  have ht : 1 ≤ t := by exact_mod_cast (show 1 ≤ (n:ℕ) from n.pos)
  have ht' := zero_lt_one.trans_le ht
  have hmass : shellMass s n = t^(1-2*s.re) := by
    rw [shellMass,Real.rpow_def_of_pos ht']
    change Real.exp ((1-2*s.re)*Real.log t) = Real.exp (Real.log t*(1-2*s.re))
    rw [mul_comm]
  have hweight : ‖heat s n‖^2 = 1/t^(2*s.re) := by
    rw [norm_heat,sq,← Real.exp_add,one_div,← Real.rpow_neg ht'.le,Real.rpow_def_of_pos ht']
    congr 1
    change -s.re*Real.log t+ -s.re*Real.log t = _
    ring
  simpa only [hmass,hweight,sameTemperatureResponse,t] using same_temperature_bounds hs ht

/-- Repeated preparation of any one elementary prime mode measures a growth rate per added quantum. -/
theorem prime_tower_response_rate {σ : ℝ} (hs : 0 < σ) (p : Nat.Primes) :
    Tendsto (fun k : ℕ => Real.log (sameTemperatureResponse σ (((p:ℕ):ℝ)^k))/(k:ℝ)) atTop
      (𝓝 ((1-2*σ)*Real.log (p:ℕ))) := by
  let a : ℝ := (p:ℕ)
  have hp : 1 < a := by exact_mod_cast p.property.one_lt
  have ht : Tendsto (fun k : ℕ => a^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hp
  have he := ((same_temperature_log_slope hs).comp ht).mul_const (Real.log a)
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  change Real.log (sameTemperatureResponse σ (a^k))/Real.log (a^k)*Real.log a = Real.log (sameTemperatureResponse σ (a^k))/(k:ℝ)
  rw [Real.log_pow]
  field_simp [(Real.log_pos hp).ne',(Nat.cast_pos.mpr hk : (0:ℝ)<k).ne']

/-- Zero rate along a single prime tower is equivalent to isometric composition on the entire gas. -/
theorem one_prime_zero_rate_iff_split {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    Tendsto (fun k : ℕ => Real.log (sameTemperatureResponse s.re (((p:ℕ):ℝ)^k))/(k:ℝ)) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have he := tendsto_nhds_unique (prime_tower_response_rate hs p) h
    have hp : (1:ℝ)<(p:ℕ) := by exact_mod_cast p.property.one_lt
    have hz := (mul_eq_zero.mp he).resolve_right (Real.log_pos hp).ne'
    linarith only [hz]
  · intro h
    simpa only [show 1-2*s.re=0 by rw [h]; norm_num,zero_mul] using prime_tower_response_rate hs p

#print axioms prime_tower_response_rate
#print axioms one_prime_zero_rate_iff_split
#print axioms same_temperature_bounds
#print axioms same_temperature_log_slope
#print axioms same_temperature_zero_iff_split
#print axioms shell_calibrated_partition_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
