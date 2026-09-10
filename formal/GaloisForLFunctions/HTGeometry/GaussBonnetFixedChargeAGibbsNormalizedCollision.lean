import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionIdentification

/-!
# The exact leading collision coefficient for every Gibbs input

After division by the slow rate, the fast spectral correction decays by
one sixteenth per transition. This makes the slow spectral energy an
unconditional limit, including inputs with no slow component.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- Collision excess normalized by the slow spectral rate. -/
def egbFixedChargeAGibbsNormalizedCollision (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  egbFixedChargeAGibbsCollisionExcess n m β E / (4 / 9 : ℝ) ^ m

/-- The normalized positive-time collision law has one exact fast correction. -/
theorem egbFixedChargeAGibbsNormalizedCollision_positive_time (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsNormalizedCollision n (m + 1) β E =
      egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 16 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  have hr : (4 / 9 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold egbFixedChargeAGibbsNormalizedCollision
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate]
  have hbase : (1 / 36 : ℝ) = (4 / 9 : ℝ) * (1 / 16 : ℝ) := by norm_num
  rw [hbase, mul_pow]
  field_simp
  <;> ring

/-- For every Gibbs input, the leading collision coefficient is its initial slow spectral energy. -/
theorem egbFixedChargeAGibbsNormalizedCollision_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsNormalizedCollision n m β E) atTop
      (nhds (egbFixedChargeAGibbsSlowModeEnergy n β E)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
  have hs := (Filter.tendsto_add_atTop_iff_nat (f := fun m : ℕ => (1 / 16 : ℝ) ^ m) 1).mpr hp
  have hA : Tendsto (fun _ : ℕ => egbFixedChargeAGibbsSlowModeEnergy n β E) atTop
      (nhds (egbFixedChargeAGibbsSlowModeEnergy n β E)) := tendsto_const_nhds
  have hB : Tendsto (fun _ : ℕ => egbFixedChargeAGibbsFastModeEnergy n β E) atTop
      (nhds (egbFixedChargeAGibbsFastModeEnergy n β E)) := tendsto_const_nhds
  have ht : Tendsto (fun m : ℕ => egbFixedChargeAGibbsSlowModeEnergy n β E +
      (1 / 16 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) atTop
        (nhds (egbFixedChargeAGibbsSlowModeEnergy n β E)) := by
    simpa only [zero_mul, add_zero] using hA.add (hs.mul hB)
  apply (Filter.tendsto_add_atTop_iff_nat
    (f := fun m => egbFixedChargeAGibbsNormalizedCollision n m β E) 1).mp
  simpa only [egbFixedChargeAGibbsNormalizedCollision_positive_time] using ht

end
end GaloisForLFunctions.HTGeometry
