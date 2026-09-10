import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTwoRateCollision

/-!
# Equilibrium classified by two spectral energies

The exact two-rate collision law gives an unconditional classification of
positive-time equilibrium for the critical thermal Gibbs kernel. The same
classification controls population uniformity and both entropy observables.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Positive-time collision excess vanishes exactly when both nonconstant spectral energies vanish. -/
theorem egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate]
  have ha := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hb := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hr : (0 : ℝ) < (4 / 9) ^ (m + 1) := by positivity
  have hs : (0 : ℝ) < (1 / 36) ^ (m + 1) := by positivity
  constructor
  · intro h
    have hA : (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E = 0 :=
      le_antisymm (by linarith [mul_nonneg hs.le hb]) (mul_nonneg hr.le ha)
    have hB : (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E = 0 :=
      le_antisymm (by linarith [mul_nonneg hr.le ha]) (mul_nonneg hs.le hb)
    exact ⟨(mul_eq_zero.mp hA).resolve_left hr.ne', (mul_eq_zero.mp hB).resolve_left hs.ne'⟩
  · rintro ⟨ha0, hb0⟩
    simp only [ha0, hb0, mul_zero, add_zero]

/-- At least one positive spectral energy is equivalent to persistent positive collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_positive_time_pos_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∨
        0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate]
  have ha := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hb := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hr : (0 : ℝ) < (4 / 9) ^ (m + 1) := by positivity
  have hs : (0 : ℝ) < (1 / 36) ^ (m + 1) := by positivity
  constructor
  · intro h
    by_cases hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E
    · exact Or.inl hA
    · right
      by_contra hB
      have ha0 := le_antisymm (le_of_not_gt hA) ha
      have hb0 := le_antisymm (le_of_not_gt hB) hb
      simp only [ha0, hb0, mul_zero, add_zero, lt_self_iff_false] at h
  · rintro (hA | hB)
    · nlinarith [mul_pos hr hA, mul_nonneg hs.le hb]
    · nlinarith [mul_nonneg hr.le ha, mul_pos hs hB]

/-- Uniformity at every positive time is determined by two initial spectral energies. -/
theorem egbFixedChargeAGibbsMarkovPopulation_uniform_two_rate_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E =
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ↔
        egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
          egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  have hf : (egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E =
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹)) ↔
      ∀ i, egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E i = ((2 : ℝ) ^ (n + 3))⁻¹ :=
    ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hf, ← egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform,
    egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff]

/-- Relative information vanishes exactly in the same two-mode equilibrium class. -/
theorem egbFixedChargeAGibbsEntropyDeficit_two_rate_zero_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsEntropyDeficit_zero_iff_uniform,
    ← egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform,
    egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff]

/-- Maximum entropy at positive time has an exact initial spectral classification. -/
theorem egbFixedChargeAGibbsEntropy_maximum_two_rate_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E) = Real.log ((2 : ℝ) ^ (n + 3)) ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  rw [egbFixedChargeAGibbsEntropy_maximum_iff_uniform,
    ← egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform,
    egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff]

end
end GaloisForLFunctions.HTGeometry
