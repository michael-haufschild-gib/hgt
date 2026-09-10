import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsAccumulatedCollision

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem information_majorant_hasSum (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => (4 / 9 : ℝ) ^ m *
      ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E))
        ((9 * (2 : ℝ) ^ (n + 3) / 5) * egbFixedChargeAGibbsCollisionExcess n 0 β E) := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 4 / 9) (by norm_num : (4 / 9 : ℝ) < 1)).mul_right
      ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E)
  norm_num at h
  have he : (9 * (2 : ℝ) ^ (n + 3) / 5) * egbFixedChargeAGibbsCollisionExcess n 0 β E =
      (9 / 5 : ℝ) * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) := by ring
  rw [he]
  exact h

/-- Every Gibbs law has finite cumulative relative information over its entire relaxation history. -/
theorem egbFixedChargeAGibbsEntropyDeficit_summable (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Summable (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E) :=
  Summable.of_nonneg_of_le (fun m => egbFixedChargeAGibbsEntropyDeficit_nonneg n m β E)
    (fun m => egbFixedChargeAGibbsEntropyDeficit_spectral_bound n m β E)
      (information_majorant_hasSum n β E).summable

/-- Initial collision excess bounds the total information carried through all transition times. -/
theorem egbFixedChargeAGibbsEntropyDeficit_total_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsEntropyDeficit n m β E) ≤
      (9 * (2 : ℝ) ^ (n + 3) / 5) * egbFixedChargeAGibbsCollisionExcess n 0 β E :=
  hasSum_le (fun m => egbFixedChargeAGibbsEntropyDeficit_spectral_bound n m β E)
    (egbFixedChargeAGibbsEntropyDeficit_summable n β E).hasSum (information_majorant_hasSum n β E)

/-- The cumulative information budget has a dimension-only upper bound. -/
theorem egbFixedChargeAGibbsEntropyDeficit_total_universal (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsEntropyDeficit n m β E) ≤ (9 / 5) * ((2 : ℝ) ^ (n + 3) - 1) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ ≤ (9 * (2 : ℝ) ^ (n + 3) / 5) * egbFixedChargeAGibbsCollisionExcess n 0 β E :=
      egbFixedChargeAGibbsEntropyDeficit_total_bound n β E
    _ ≤ (9 * (2 : ℝ) ^ (n + 3) / 5) * (1 - ((2 : ℝ) ^ (n + 3))⁻¹) :=
      mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsCollisionExcess_le_uniform_complement n 0 β E)
        (by positivity)
    _ = _ := by field_simp <;> ring

/-- Squared Hellinger distinguishability is summable over the complete Gibbs history. -/
theorem egbFixedChargeAGibbsHellinger_sq_summable (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m => finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun m => egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E)
      (egbFixedChargeAGibbsEntropyDeficit_summable n β E)

/-- Total squared distinguishability is bounded by the same finite information budget. -/
theorem egbFixedChargeAGibbsHellinger_sq_total_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2) ≤ (9 / 5) * ((2 : ℝ) ^ (n + 3) - 1) := by
  exact (hasSum_le (fun m => egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E)
    (egbFixedChargeAGibbsHellinger_sq_summable n β E).hasSum
      (egbFixedChargeAGibbsEntropyDeficit_summable n β E).hasSum).trans
        (egbFixedChargeAGibbsEntropyDeficit_total_universal n β E)

end
end GaloisForLFunctions.HTGeometry
