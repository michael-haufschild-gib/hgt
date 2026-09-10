import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeApplications

/-! # Exact dimensional boundary of the three-sector Gibbs family -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- The inverse dyadic grid size tends to zero by an exact geometric identity. -/
theorem egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ (n + 3))⁻¹) atTop (nhds 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have he (n : ℕ) : ((2 : ℝ) ^ (n + 3))⁻¹ = (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n := by
    rw [pow_add (2 : ℝ) n 3, mul_inv_rev, ← inv_pow (2 : ℝ) n]
    norm_num
  simpa only [he, mul_zero] using ht.const_mul (1 / 8 : ℝ)

/-- The erased energy differs from its boundary value by one exact inverse-grid term. -/
theorem egbFixedChargeAGibbsSpike_discarded_boundary_identity (n : ℕ) :
    egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      (1 / 4 : ℝ) - (5 / 4 : ℝ) * ((2 : ℝ) ^ (n + 3))⁻¹ := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsSpike_discarded_energy]
  field_simp [hn]
  <;> ring

/-- The erased Fourier sector tends to the positive boundary mass one quarter. -/
theorem egbFixedChargeAGibbsSpike_discarded_tendsto_quarter :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds (1 / 4 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (nhds (1 / 4 : ℝ)) := tendsto_const_nhds
  have h := hc.sub (egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero.const_mul (5 / 4 : ℝ))
  simpa only [egbFixedChargeAGibbsSpike_discarded_boundary_identity, mul_zero, sub_zero] using h

/-- The slow energy vanishes with inverse grid size. -/
theorem egbFixedChargeAGibbsSpike_slow_tendsto_zero :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds 0) := by
  have he (n : ℕ) : egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((2 : ℝ) ^ (n + 3))⁻¹ * (1 / 2 : ℝ) := by
    rw [egbFixedChargeAGibbsSpike_slow_energy]
    ring
  simpa only [he, zero_mul] using egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero.mul_const (1 / 2 : ℝ)

/-- The fast energy vanishes at the same dimensional rate as the slow energy. -/
theorem egbFixedChargeAGibbsSpike_fast_tendsto_zero :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds 0) := by
  simpa only [egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy] using
    egbFixedChargeAGibbsSpike_slow_tendsto_zero

/-- Initial collision excess retains a positive limiting value even as all surviving sectors vanish. -/
theorem egbFixedChargeAGibbsSpike_initial_collision_tendsto_quarter :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds (1 / 4 : ℝ)) := by
  have h := (egbFixedChargeAGibbsSpike_discarded_tendsto_quarter.add
    egbFixedChargeAGibbsSpike_slow_tendsto_zero).add egbFixedChargeAGibbsSpike_fast_tendsto_zero
  simpa only [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition, add_zero] using h

/-- Every fixed positive-time collision value vanishes in the dimensional limit. -/
theorem egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds 0) := by
  have he (n : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((4 / 9 : ℝ) ^ (m + 1) + (1 / 36 : ℝ) ^ (m + 1)) *
        egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) := by
    rw [egbFixedChargeAGibbsSpike_collision_positive_time, egbFixedChargeAGibbsSpike_slow_energy]
    ring
  simpa only [he, mul_zero] using egbFixedChargeAGibbsSpike_slow_tendsto_zero.const_mul
    ((4 / 9 : ℝ) ^ (m + 1) + (1 / 36 : ℝ) ^ (m + 1))

/-- The entire collision history converges to the moments of a one-quarter atom at zero. -/
theorem egbFixedChargeAGibbsSpike_full_collision_limit (m : ℕ) :
    Tendsto (fun n : ℕ => egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSpikeEnergy n))
      atTop (nhds ((0 : ℝ) ^ m / 4)) := by
  cases m with
  | zero => simpa using egbFixedChargeAGibbsSpike_initial_collision_tendsto_quarter
  | succ m => simpa using egbFixedChargeAGibbsSpike_positive_collision_tendsto_zero m

/-- Multiplying positive-time collision excess by grid size recovers one exact nonzero history. -/
theorem egbFixedChargeAGibbsSpike_rescaled_positive_collision (n m : ℕ) :
    (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((4 / 9 : ℝ) ^ (m + 1) + (1 / 36 : ℝ) ^ (m + 1)) / 2 := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsSpike_collision_positive_time]
  field_simp [hn]
  <;> ring

/-- The first dimensional correction to every full-history moment is exact and independent of dimension. -/
theorem egbFixedChargeAGibbsSpike_rescaled_full_collision_error (n m : ℕ) :
    (2 : ℝ) ^ (n + 3) * (egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSpikeEnergy n) -
      (0 : ℝ) ^ m / 4) =
      -(5 / 4 : ℝ) * (0 : ℝ) ^ m + (4 / 9 : ℝ) ^ m / 2 + (1 / 36 : ℝ) ^ m / 2 := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsSpike_collision_full]
  field_simp [hn]
  <;> ring

end
end GaloisForLFunctions.HTGeometry
