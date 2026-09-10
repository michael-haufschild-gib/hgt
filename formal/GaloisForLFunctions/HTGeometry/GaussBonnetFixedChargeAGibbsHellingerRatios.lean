import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHellingerPrefactor

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Topology

/-- The exact squared-Hellinger to collision ratio approaches half the grid dimension. -/
theorem egbFixedChargeAGibbsSlow_hellinger_collision_ratio_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsSlowHellingerSquared n m /
      egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)) atTop
        (nhds ((2 : ℝ) ^ (n + 3) / 4)) := by
  have hp := egbFixedChargeAGibbsSlow_collision_initial_pos n
  have hc : Tendsto (fun _ : ℕ => egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))
      atTop (nhds (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) := tendsto_const_nhds
  have h := (egbFixedChargeAGibbsSlowNormalizedHellinger_limit n).div hc hp.ne'
  have he (m : ℕ) : egbFixedChargeAGibbsSlowHellingerSquared n m /
      egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
        egbFixedChargeAGibbsSlowNormalizedHellinger n m /
          egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) := by
    unfold egbFixedChargeAGibbsSlowNormalizedHellinger
    rw [egbFixedChargeAGibbsSlow_collision_exact]
    ring
  simp_rw [he]
  have hv : egbFixedChargeAGibbsSlowHellingerPrefactor n /
      egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (2 : ℝ) ^ (n + 3) / 4 := by
    unfold egbFixedChargeAGibbsSlowHellingerPrefactor
    field_simp
  rw [hv] at h
  exact h

/-- The actual consecutive squared-Hellinger ratio tends to the sharp spectral base. -/
theorem egbFixedChargeAGibbsSlow_hellinger_step_ratio_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsSlowHellingerSquared n (m + 1) /
      egbFixedChargeAGibbsSlowHellingerSquared n m) atTop (nhds (4 / 9 : ℝ)) := by
  have h := egbFixedChargeAGibbsSlowNormalizedHellinger_limit n
  have hs := (Filter.tendsto_add_atTop_iff_nat
    (f := fun m => egbFixedChargeAGibbsSlowNormalizedHellinger n m) 1).mpr h
  have hc : Tendsto (fun _ : ℕ => (4 / 9 : ℝ)) atTop (nhds (4 / 9 : ℝ)) := tendsto_const_nhds
  have hr := hc.mul (hs.div h (egbFixedChargeAGibbsSlowHellingerPrefactor_pos n).ne')
  have he (m : ℕ) : egbFixedChargeAGibbsSlowHellingerSquared n (m + 1) /
      egbFixedChargeAGibbsSlowHellingerSquared n m =
        (4 / 9 : ℝ) * (egbFixedChargeAGibbsSlowNormalizedHellinger n (m + 1) /
          egbFixedChargeAGibbsSlowNormalizedHellinger n m) := by
    have hq : (4 / 9 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    have hd := (egbFixedChargeAGibbsSlow_hellinger_sq_pos n m).ne'
    unfold egbFixedChargeAGibbsSlowNormalizedHellinger
    rw [pow_succ (4 / 9 : ℝ) m]
    field_simp
  simp_rw [he]
  simpa only [Pi.div_def, div_self (egbFixedChargeAGibbsSlowHellingerPrefactor_pos n).ne', mul_one] using hr

/-- Each late transition consumes a fraction approaching five ninths of the remaining squared Hellinger distance. -/
theorem egbFixedChargeAGibbsSlow_hellinger_loss_ratio_limit (n : ℕ) :
    Tendsto (fun m =>
      (egbFixedChargeAGibbsSlowHellingerSquared n m -
        egbFixedChargeAGibbsSlowHellingerSquared n (m + 1)) /
          egbFixedChargeAGibbsSlowHellingerSquared n m) atTop
      (nhds (5 / 9 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := hc.sub (egbFixedChargeAGibbsSlow_hellinger_step_ratio_limit n)
  have he (m : ℕ) :
      (egbFixedChargeAGibbsSlowHellingerSquared n m -
        egbFixedChargeAGibbsSlowHellingerSquared n (m + 1)) /
          egbFixedChargeAGibbsSlowHellingerSquared n m =
        1 - egbFixedChargeAGibbsSlowHellingerSquared n (m + 1) /
          egbFixedChargeAGibbsSlowHellingerSquared n m := by
    have hh : egbFixedChargeAGibbsSlowHellingerSquared n m ≠ 0 :=
      (egbFixedChargeAGibbsSlow_hellinger_sq_pos n m).ne'
    rw [sub_div, div_self hh]
  simp_rw [he]
  convert h using 1 <;> norm_num

/-- Relative entropy is asymptotically twice squared Hellinger distance. -/
theorem egbFixedChargeAGibbsSlow_information_hellinger_ratio_limit (n : ℕ) :
    Tendsto (fun m =>
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) /
        egbFixedChargeAGibbsSlowHellingerSquared n m) atTop (nhds (2 : ℝ)) := by
  have h := (egbFixedChargeAGibbsSlowNormalizedInformation_limit n).div
    (egbFixedChargeAGibbsSlowNormalizedHellinger_limit n)
    (egbFixedChargeAGibbsSlowHellingerPrefactor_pos n).ne'
  have he (m : ℕ) :
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) /
        egbFixedChargeAGibbsSlowHellingerSquared n m =
      egbFixedChargeAGibbsSlowNormalizedInformation n m /
        egbFixedChargeAGibbsSlowNormalizedHellinger n m := by
    have hq : (4 / 9 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    have hh : egbFixedChargeAGibbsSlowHellingerSquared n m ≠ 0 :=
      (egbFixedChargeAGibbsSlow_hellinger_sq_pos n m).ne'
    unfold egbFixedChargeAGibbsSlowNormalizedInformation egbFixedChargeAGibbsSlowNormalizedHellinger
    field_simp
  have hv : egbFixedChargeAGibbsSlowInformationPrefactor n /
      egbFixedChargeAGibbsSlowHellingerPrefactor n = 2 := by
    have hp := (egbFixedChargeAGibbsSlow_collision_initial_pos n).ne'
    unfold egbFixedChargeAGibbsSlowInformationPrefactor egbFixedChargeAGibbsSlowHellingerPrefactor
    field_simp
    norm_num
  simp_rw [he]
  simpa only [Pi.div_def, hv] using h

end
end GaloisForLFunctions.HTGeometry
