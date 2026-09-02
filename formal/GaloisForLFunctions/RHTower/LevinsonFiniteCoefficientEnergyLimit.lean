import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortMainLimit
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogAsymptotic
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongRangeSplit

/-!
# Total finite Levinson coefficient energy at the `49/100` schedule

The exact short/long split combines the newly evaluated short lcm energy with the existing included
long-tail asymptotic.
-/

open Filter Topology Finset

namespace RHTower

noncomputable section

/-- Complete finite critical-detector convolution energy at reciprocal `49/100` tuning. -/
theorem tendsto_levinsonCriticalDetectorFiniteEnergy_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      ∑ r : Fin (N ^ 100 * N ^ 49),
        levinsonCriticalDetectorFiniteEnergyTerm
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) r)
      atTop (𝓝 (19751 / 14700 : ℝ)) := by
  have hs := Sieve.tendsto_barbanVehovShortEnergyLcm_fortyNine_reciprocal
  have hl := Sieve.tendsto_levinsonCriticalDetectorLongEnergy_fortyNine_reciprocal
  have hsum := hs.add hl
  have hsum' : Tendsto (fun N : ℕ =>
      Sieve.barbanVehovShortEnergyLcm
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) +
        levinsonCriticalDetectorLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 (19751 / 14700 : ℝ)) := by
    convert hsum using 1
    all_goals norm_num
  refine hsum'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hM : 1 < N ^ 49 := by
    have hpow : N ≤ N ^ 49 := by
      calc
        N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hNpos 48)
        _ = N ^ 49 := by ring
    omega
  have hML : N ^ 49 ≤ N ^ 100 := Nat.pow_le_pow_right hNpos (by omega)
  rw [sum_levinsonCriticalDetectorFiniteEnergyTerm_eq_short_add_long _ _ _
    (le_of_lt hM)]
  rw [Sieve.sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_shortEnergyLcm
    _ hM hML]

end

end RHTower
