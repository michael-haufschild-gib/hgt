import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeSpectralEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHankelRank
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionCDD

/-! # An explicit Gibbs realization of three-atom erasure geometry -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The complete spike collision history has an explicit three-rate formula on every grid. -/
theorem egbFixedChargeAGibbsSpike_collision_full (n m : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((0 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 5) +
        2 * (4 / 9 : ℝ) ^ m + 2 * (1 / 36 : ℝ) ^ m) /
        (4 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsCollisionExcess_full_time_three_rate,
    egbFixedChargeAGibbsSpike_discarded_energy, egbFixedChargeAGibbsSpike_slow_energy,
    egbFixedChargeAGibbsSpike_fast_energy]
  field_simp [hn]
  <;> ring

/-- After the first transition the collision history is the equal-weight sum of the two surviving rates. -/
theorem egbFixedChargeAGibbsSpike_collision_positive_time (n m : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((4 / 9 : ℝ) ^ (m + 1) + (1 / 36 : ℝ) ^ (m + 1)) /
        (2 * (2 : ℝ) ^ (n + 3)) := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate,
    egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy]
  ring

/-- The rank-three to rank-two transition is realized by an explicit Gibbs energy for every grid and every positive shift. -/
theorem egbFixedChargeAGibbsSpike_hankel_rank_drop (n o k : ℕ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n (k + 3) 1 (egbFixedChargeAGibbsSpikeEnergy n)).rank = 3 ∧
      (egbFixedChargeAGibbsCollisionHankelMatrix n o (k + 3) 1 (egbFixedChargeAGibbsSpikeEnergy n)).rank = 2 := by
  exact (egbFixedChargeAGibbsCollisionHankel_rank_drop_iff n o k 1
    (egbFixedChargeAGibbsSpikeEnergy n)).mpr (egbFixedChargeAGibbsSpike_three_energies_pos n)

/-- The first three-dimensional Gram volume has a closed positive formula for the explicit spike state. -/
theorem egbFixedChargeAGibbsSpike_hankel_three_det (n : ℕ) :
    (egbFixedChargeAGibbsFullCollisionHankelMatrix n 3 1 (egbFixedChargeAGibbsSpikeEnergy n)).det =
      25 * ((2 : ℝ) ^ (n + 3) - 5) / (15116544 * ((2 : ℝ) ^ (n + 3)) ^ 3) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsFullCollisionHankelMatrix_three_det,
    egbFixedChargeAGibbsSpike_discarded_energy, egbFixedChargeAGibbsSpike_slow_energy,
    egbFixedChargeAGibbsSpike_fast_energy]
  field_simp [hn]
  <;> ring

/-- The explicit three-sector Gibbs family produces a closed endpoint-plus-two-shell CDD phase. -/
theorem egbFixedChargeAGibbsSpike_full_CDD_phase (n : ℕ) (θ : ℝ) :
    egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsSpikeEnergy n) θ =
      2 * ((2 : ℝ) ^ (n + 3) - 5) / (2 : ℝ) ^ (n + 3) * Real.sinh θ +
      3 / (2 : ℝ) ^ (n + 3) * Real.arctan ((12 / 13 : ℝ) * Real.sinh θ) +
      12 / (2 : ℝ) ^ (n + 3) * Real.arctan ((12 / 37 : ℝ) * Real.sinh θ) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsFullCollisionCDDPhase_arctan,
    egbFixedChargeAGibbsSpike_discarded_energy, egbFixedChargeAGibbsSpike_slow_energy,
    egbFixedChargeAGibbsSpike_fast_energy]
  field_simp [hn]
  <;> ring

end
end GaloisForLFunctions.HTGeometry
