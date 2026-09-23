import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeFourier
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullTimeCollision
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTParseval

/-! # Exact positive energy in every thermal spectral sector -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open QuantumAlg

private theorem inv_sqrt_norm_sq (n : ℕ) :
    ‖invSqrtN (n + 3)‖ ^ (2 : ℕ) = ((2 : ℝ) ^ (n + 3))⁻¹ := by
  rw [norm_invSqrtN, inv_pow (Real.sqrt ((2 : ℝ) ^ (n + 3))) 2, Real.sq_sqrt (by positivity)]

private theorem half_inv_sqrt_norm_sq (n : ℕ) :
    ‖invSqrtN (n + 3) / 2‖ ^ (2 : ℕ) = ((2 : ℝ) ^ (n + 3))⁻¹ / 4 := by
  rw [norm_div, div_pow]
  norm_num [inv_sqrt_norm_sq]

/-- Every nonzero Fourier frequency carries the same strictly positive energy. -/
theorem egbFixedChargeAGibbsSpike_fourier_norm_sq (n : ℕ) (k : Fin (2 ^ (n + 3))) :
    ‖egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ)) k‖ ^ (2 : ℕ) =
      if k = 0 then ((2 : ℝ) ^ (n + 3))⁻¹ else ((2 : ℝ) ^ (n + 3))⁻¹ / 4 := by
  rw [egbFixedChargeAGibbsSpike_fourier_coordinates]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk]
    exact inv_sqrt_norm_sq n
  · rw [if_neg hk, if_neg hk]
    exact half_inv_sqrt_norm_sq n

/-- The constructed Gibbs state excites every full Fourier mode, including every discarded frequency. -/
theorem egbFixedChargeAGibbsSpike_fourier_ne_zero (n : ℕ) (k : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ)) k ≠ 0 := by
  have hn : invSqrtN (n + 3) ≠ 0 := by
    unfold invSqrtN
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
  rw [egbFixedChargeAGibbsSpike_fourier_coordinates]
  split_ifs
  · exact hn
  · exact div_ne_zero hn (by norm_num)

/-- The slow sector of the spike Gibbs input has exact energy one over twice the grid size. -/
theorem egbFixedChargeAGibbsSpike_slow_energy (n : ℕ) :
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      1 / (2 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsSlowModeEnergy, egbFixedChargeAGibbsSpike_fourier_moments n 1,
    egbFixedChargeAGibbsSpike_fourier_moments n 4,
    if_neg (show (1 : Fin 5) ≠ 0 by omega), if_neg (show (4 : Fin 5) ≠ 0 by omega)]
  simp only [half_inv_sqrt_norm_sq]
  field_simp [hn]
  <;> ring

/-- The fast and slow sectors have equal exact initial energy. -/
theorem egbFixedChargeAGibbsSpike_fast_energy (n : ℕ) :
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      1 / (2 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsFastModeEnergy, egbFixedChargeAGibbsSpike_fourier_moments n 2,
    egbFixedChargeAGibbsSpike_fourier_moments n 3,
    if_neg (show (2 : Fin 5) ≠ 0 by omega), if_neg (show (3 : Fin 5) ≠ 0 by omega)]
  simp only [half_inv_sqrt_norm_sq]
  field_simp [hn]
  <;> ring

/-- Summing every Fourier coordinate gives an exact energy formula with no omitted frequencies. -/
theorem egbFixedChargeAGibbsSpike_total_fourier_energy (n : ℕ) :
    (∑ k, ‖egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ)) k‖ ^ (2 : ℕ)) =
      ((2 : ℝ) ^ (n + 3) + 3) / (4 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (∑ k, ‖egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ)) k‖ ^ (2 : ℕ)) =
      ∑ k : Fin (2 ^ (n + 3)),
        (((2 : ℝ) ^ (n + 3))⁻¹ / 4 + if k = 0 then 3 * ((2 : ℝ) ^ (n + 3))⁻¹ / 4 else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [egbFixedChargeAGibbsSpike_fourier_norm_sq]
    by_cases hk : k = 0 <;> simp [hk] <;> ring
  rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  simp
  <;> field_simp [hn]
  <;> ring

/-- Initial collision excess is exactly the nonconstant Fourier energy of the spike law. -/
theorem egbFixedChargeAGibbsSpike_initial_collision (n : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((2 : ℝ) ^ (n + 3) - 1) / (4 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp := egbFixedChargeACriticalFourierCoordinates_parseval n
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ))
  rw [egbFixedChargeAGibbsSpike_total_fourier_energy] at hp
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  rw [egbFixedChargeAGibbsCollisionExcess_identity, egbFixedChargeAGibbsMarkovPopulation_zero, ← hp]
  field_simp [hn]
  <;> ring

/-- The discarded Fourier modes carry the remaining exact positive energy. -/
theorem egbFixedChargeAGibbsSpike_discarded_energy (n : ℕ) :
    egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      ((2 : ℝ) ^ (n + 3) - 5) / (4 * (2 : ℝ) ^ (n + 3)) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp := egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition n 1 (egbFixedChargeAGibbsSpikeEnergy n)
  have hr : egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSpikeEnergy n) -
      egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) -
      egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) := by linarith
  rw [hr, egbFixedChargeAGibbsSpike_initial_collision,
    egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy]
  field_simp [hn]
  <;> ring

/-- All three sectors are strictly positive for this explicit Gibbs landscape on every grid. -/
theorem egbFixedChargeAGibbsSpike_three_energies_pos (n : ℕ) :
    0 < egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) ∧
    0 < egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) ∧
    0 < egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) := by
  have hnat : 8 ≤ 2 ^ (n + 3) := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
    rw [pow_add]
    norm_num
    omega
  have hN : (8 : ℝ) ≤ (2 : ℝ) ^ (n + 3) := by exact_mod_cast hnat
  rw [egbFixedChargeAGibbsSpike_discarded_energy,
    egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy]
  refine ⟨div_pos (by linarith) (by positivity), ?_, ?_⟩ <;> positivity

end
end GaloisForLFunctions.HTGeometry
