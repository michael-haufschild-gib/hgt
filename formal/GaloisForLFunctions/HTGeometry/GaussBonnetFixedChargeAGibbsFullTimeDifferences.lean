import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullTimeCollision
import GaloisForLFunctions.HTGeometry.HausdorffPositiveCddCone

/-! # Recovering erased information from difference order -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- Signed forward difference of the full collision history, including its initial value. -/
def egbFixedChargeAGibbsFullCollisionSignedDifference (n m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (-1 : ℝ) ^ k * ((fwdDiff 1)^[k] (fun j : ℕ => egbFixedChargeAGibbsCollisionExcess n j β E) m)

private theorem full_collision_geometric (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m β E) =
      (fun m : ℕ => ∑ i : Fin 3,
        (![egbFixedChargeAGibbsDiscardedModeEnergy n β E,
          egbFixedChargeAGibbsSlowModeEnergy n β E, egbFixedChargeAGibbsFastModeEnergy n β E] i) *
        (![(0 : ℝ), (4 / 9 : ℝ), (1 / 36 : ℝ)] i) ^ m) := by
  funext m
  rw [egbFixedChargeAGibbsCollisionExcess_full_time_three_rate, Fin.sum_univ_three]
  change _ = egbFixedChargeAGibbsDiscardedModeEnergy n β E * (0 : ℝ) ^ m +
    egbFixedChargeAGibbsSlowModeEnergy n β E * (4 / 9 : ℝ) ^ m +
    egbFixedChargeAGibbsFastModeEnergy n β E * (1 / 36 : ℝ) ^ m
  ring

/-- All full-history difference orders retain exactly the same zero-rate contribution. -/
theorem egbFixedChargeAGibbsFullCollisionSignedDifference_formula (n m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionSignedDifference n m k β E =
      (0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E +
      (5 / 9 : ℝ) ^ k * (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (35 / 36 : ℝ) ^ k * (1 / 36 : ℝ) ^ m * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsFullCollisionSignedDifference, full_collision_geometric,
    fwdDiff_iter_geometricCombination, Fin.sum_univ_three]
  change (-1 : ℝ) ^ k *
    (egbFixedChargeAGibbsDiscardedModeEnergy n β E * (((0 : ℝ) - 1) ^ k * (0 : ℝ) ^ m) +
     egbFixedChargeAGibbsSlowModeEnergy n β E * (((4 / 9 : ℝ) - 1) ^ k * (4 / 9 : ℝ) ^ m) +
     egbFixedChargeAGibbsFastModeEnergy n β E * (((1 / 36 : ℝ) - 1) ^ k * (1 / 36 : ℝ) ^ m)) = _
  have hz : (-1 : ℝ) ^ k * ((0 : ℝ) - 1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hr : (-1 : ℝ) ^ k * ((4 / 9 : ℝ) - 1) ^ k = (5 / 9 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  have hs : (-1 : ℝ) ^ k * ((1 / 36 : ℝ) - 1) ^ k = (35 / 36 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ) ^ k * ((0 : ℝ) - 1) ^ k) * (0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E +
        ((-1 : ℝ) ^ k * ((4 / 9 : ℝ) - 1) ^ k) * (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsSlowModeEnergy n β E +
        ((-1 : ℝ) ^ k * ((1 / 36 : ℝ) - 1) ^ k) * (1 / 36 : ℝ) ^ m * egbFixedChargeAGibbsFastModeEnergy n β E := by ring
    _ = _ := by rw [hz, hr, hs]; ring

/-- Signed differences of the full history are nonnegative, including the initial boundary. -/
theorem egbFixedChargeAGibbsFullCollisionSignedDifference_nonneg (n m k : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 ≤ egbFixedChargeAGibbsFullCollisionSignedDifference n m k β E := by
  rw [egbFixedChargeAGibbsFullCollisionSignedDifference_formula]
  have hR := egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hz : 0 ≤ (0 : ℝ) ^ m := pow_nonneg (le_refl 0) m
  have hr : 0 ≤ (5 / 9 : ℝ) ^ k * (4 / 9 : ℝ) ^ m := by positivity
  have hs : 0 ≤ (35 / 36 : ℝ) ^ k * (1 / 36 : ℝ) ^ m := by positivity
  exact add_nonneg (add_nonneg (mul_nonneg hz hR) (mul_nonneg hr hA)) (mul_nonneg hs hB)

/-- Increasing difference order isolates the zero-rate atom at every observation time. -/
theorem egbFixedChargeAGibbsFullCollisionSignedDifference_order_limit (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun k : ℕ => egbFixedChargeAGibbsFullCollisionSignedDifference n m k β E) atTop
      (nhds ((0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E)) := by
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 5 / 9) (by norm_num : (5 / 9 : ℝ) < 1)
  have hs := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 35 / 36) (by norm_num : (35 / 36 : ℝ) < 1)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E) atTop
      (nhds ((0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E)) := tendsto_const_nhds
  have h := (hz.add
    ((hr.mul_const ((4 / 9 : ℝ) ^ m)).mul_const (egbFixedChargeAGibbsSlowModeEnergy n β E))).add
    ((hs.mul_const ((1 / 36 : ℝ) ^ m)).mul_const (egbFixedChargeAGibbsFastModeEnergy n β E))
  simpa only [egbFixedChargeAGibbsFullCollisionSignedDifference_formula, zero_mul, add_zero] using h

/-- The erased spectral energy is the exact limit of initial signed differences. -/
theorem egbFixedChargeAGibbsDiscardedModeEnergy_difference_reconstruction (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun k : ℕ => egbFixedChargeAGibbsFullCollisionSignedDifference n 0 k β E) atTop
      (nhds (egbFixedChargeAGibbsDiscardedModeEnergy n β E)) := by
  simpa using egbFixedChargeAGibbsFullCollisionSignedDifference_order_limit n 0 β E

end
end GaloisForLFunctions.HTGeometry
