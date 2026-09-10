import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationPrefactor

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Topology

/-- The exact relative-information to collision ratio approaches half the grid dimension. -/
theorem egbFixedChargeAGibbsSlow_information_collision_ratio_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) /
      egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)) atTop
        (nhds ((2 : ℝ) ^ (n + 3) / 2)) := by
  have hp := egbFixedChargeAGibbsSlow_collision_initial_pos n
  have hc : Tendsto (fun _ : ℕ => egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))
      atTop (nhds (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) := tendsto_const_nhds
  have h := (egbFixedChargeAGibbsSlowNormalizedInformation_limit n).div hc hp.ne'
  have he (m : ℕ) : egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) /
      egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
        egbFixedChargeAGibbsSlowNormalizedInformation n m /
          egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) := by
    unfold egbFixedChargeAGibbsSlowNormalizedInformation
    rw [egbFixedChargeAGibbsSlow_collision_exact]
    ring
  simp_rw [he]
  have hv : egbFixedChargeAGibbsSlowInformationPrefactor n /
      egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (2 : ℝ) ^ (n + 3) / 2 := by
    unfold egbFixedChargeAGibbsSlowInformationPrefactor
    field_simp
  rw [hv] at h
  exact h

/-- The actual consecutive relative-information ratio tends to the sharp spectral base. -/
theorem egbFixedChargeAGibbsSlow_information_step_ratio_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n) /
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n)) atTop (nhds (4 / 9 : ℝ)) := by
  have h := egbFixedChargeAGibbsSlowNormalizedInformation_limit n
  have hs := (Filter.tendsto_add_atTop_iff_nat
    (f := fun m => egbFixedChargeAGibbsSlowNormalizedInformation n m) 1).mpr h
  have hc : Tendsto (fun _ : ℕ => (4 / 9 : ℝ)) atTop (nhds (4 / 9 : ℝ)) := tendsto_const_nhds
  have hr := hc.mul (hs.div h (egbFixedChargeAGibbsSlowInformationPrefactor_pos n).ne')
  have he (m : ℕ) : egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n) /
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (4 / 9 : ℝ) * (egbFixedChargeAGibbsSlowNormalizedInformation n (m + 1) /
          egbFixedChargeAGibbsSlowNormalizedInformation n m) := by
    have hq : (4 / 9 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    have hd := (egbFixedChargeAGibbsSlow_information_pos n m).ne'
    unfold egbFixedChargeAGibbsSlowNormalizedInformation
    rw [pow_succ (4 / 9 : ℝ) m]
    field_simp
    <;> ring
  simp_rw [he]
  simpa only [Pi.div_def, div_self (egbFixedChargeAGibbsSlowInformationPrefactor_pos n).ne', mul_one] using hr

/-- Each late transition consumes a fraction approaching five ninths of the remaining information. -/
theorem egbFixedChargeAGibbsSlow_information_loss_ratio_limit (n : ℕ) :
    Tendsto (fun m =>
      (egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
        egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n)) /
          egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n)) atTop
      (nhds (5 / 9 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := hc.sub (egbFixedChargeAGibbsSlow_information_step_ratio_limit n)
  have he (m : ℕ) :
      (egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
        egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n)) /
          egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
        1 - egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsSlowEnergy n) /
          egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) := by
    rw [sub_div, div_self (egbFixedChargeAGibbsSlow_information_pos n m).ne']
  simp_rw [he]
  convert h using 1 <;> norm_num

end
end GaloisForLFunctions.HTGeometry
