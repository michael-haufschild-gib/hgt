import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsEntropyDeficitBounds

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Probability normalization gives an energy-independent bound for collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_le_uniform_complement (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E ≤ 1 - ((2 : ℝ) ^ (n + 3))⁻¹ := by
  rw [egbFixedChargeAGibbsCollisionExcess_identity]
  apply sub_le_sub_right
  calc
    (∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i ^ 2) ≤
        ∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
          egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E j) hi
      rw [egbFixedChargeAGibbsMarkovPopulation_mass] at hp
      nlinarith [egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E i]
    _ = 1 := egbFixedChargeAGibbsMarkovPopulation_mass n m β E

/-- Remaining information after an even number of transitions has an explicit geometric bound. -/
theorem egbFixedChargeAGibbsEntropyDeficit_even_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n (2 * m) β E ≤
      (25 / 36 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) := by
  calc
    _ ≤ (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n (2 * m) β E :=
      egbFixedChargeAGibbsEntropyDeficit_collision_upper n (2 * m) β E
    _ ≤ (2 : ℝ) ^ (n + 3) *
        ((25 / 36 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E) :=
      mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsCollisionExcess_even_bound n m β E)
        (by positivity)
    _ = _ := by ring

/-- The same information bound holds at the following odd time. -/
theorem egbFixedChargeAGibbsEntropyDeficit_odd_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n (2 * m + 1) β E ≤
      (25 / 36 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) :=
  (egbFixedChargeAGibbsEntropyDeficit_antitone n β E (by omega)).trans
    (egbFixedChargeAGibbsEntropyDeficit_even_bound n m β E)

/-- A uniform bound controls information loss for every energy landscape and inverse temperature. -/
theorem egbFixedChargeAGibbsEntropyDeficit_even_universal (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n (2 * m) β E ≤
      (25 / 36 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := mul_le_mul_of_nonneg_left
    (egbFixedChargeAGibbsCollisionExcess_le_uniform_complement n 0 β E)
    (show 0 ≤ (2 : ℝ) ^ (n + 3) by positivity)
  have he : (2 : ℝ) ^ (n + 3) * (1 - ((2 : ℝ) ^ (n + 3))⁻¹) =
      (2 : ℝ) ^ (n + 3) - 1 := by field_simp
  rw [he] at h
  exact (egbFixedChargeAGibbsEntropyDeficit_even_bound n m β E).trans
    (mul_le_mul_of_nonneg_left h (by positivity))

/-- The energy-independent estimate also applies to every odd time. -/
theorem egbFixedChargeAGibbsEntropyDeficit_odd_universal (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n (2 * m + 1) β E ≤
      (25 / 36 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) :=
  (egbFixedChargeAGibbsEntropyDeficit_antitone n β E (by omega)).trans
    (egbFixedChargeAGibbsEntropyDeficit_even_universal n m β E)

/-- The contraction estimate is an explicit lower bound on entropy production. -/
theorem egbFixedChargeAGibbsEntropy_geometric_lower (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (n + 3 : ℝ) * Real.log 2 - (25 / 36 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) ≤
      entropy (egbFixedChargeAGibbsMarkovPopulation n (2 * m) β E) := by
  have h := egbFixedChargeAGibbsEntropyDeficit_even_universal n m β E
  rw [egbFixedChargeAGibbsEntropyDeficit_identity] at h
  linarith

end
end GaloisForLFunctions.HTGeometry
