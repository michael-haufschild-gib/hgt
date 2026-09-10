import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationRatios

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem geometric_scaled_sum (A : ℝ) :
    HasSum (fun m : ℕ => (4 / 9 : ℝ) ^ m * A) ((9 / 5) * A) := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 4 / 9) (by norm_num : (4 / 9 : ℝ) < 1)).mul_right A
  norm_num at h
  exact h

/-- The total collision excess accumulated over all transitions is finite. -/
theorem egbFixedChargeAGibbsCollisionExcess_summable (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Summable (fun m => egbFixedChargeAGibbsCollisionExcess n m β E) :=
  Summable.of_nonneg_of_le (fun m => egbFixedChargeAGibbsCollisionExcess_nonneg n m β E)
    (fun m => egbFixedChargeAGibbsCollisionExcess_spectral_bound n m β E)
      (geometric_scaled_sum (egbFixedChargeAGibbsCollisionExcess n 0 β E)).summable

/-- Integrated collision excess is at most nine fifths of its initial value. -/
theorem egbFixedChargeAGibbsCollisionExcess_total_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsCollisionExcess n m β E) ≤
      (9 / 5) * egbFixedChargeAGibbsCollisionExcess n 0 β E :=
  hasSum_le (fun m => egbFixedChargeAGibbsCollisionExcess_spectral_bound n m β E)
    (egbFixedChargeAGibbsCollisionExcess_summable n β E).hasSum
      (geometric_scaled_sum (egbFixedChargeAGibbsCollisionExcess n 0 β E))

/-- The slow Gibbs state attains the integrated collision bound exactly. -/
theorem egbFixedChargeAGibbsSlow_collision_hasSum (n : ℕ) :
    HasSum (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n))
      ((9 / 5) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) := by
  have he : (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)) =
      (fun m : ℕ => (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) :=
    funext (egbFixedChargeAGibbsSlow_collision_exact n)
  rw [he]
  exact geometric_scaled_sum _

/-- The optimal uniform integrated collision coefficient is exactly nine fifths. -/
theorem egbFixedChargeAGibbsCollisionExcess_total_sharp (n : ℕ) (B : ℝ) :
    (∀ (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ),
      (∑' m : ℕ, egbFixedChargeAGibbsCollisionExcess n m β E) ≤
        B * egbFixedChargeAGibbsCollisionExcess n 0 β E) ↔ 9 / 5 ≤ B := by
  constructor
  · intro h
    have hw := h 1 (egbFixedChargeAGibbsSlowEnergy n)
    rw [(egbFixedChargeAGibbsSlow_collision_hasSum n).tsum_eq] at hw
    nlinarith [egbFixedChargeAGibbsSlow_collision_initial_pos n]
  · intro h β E
    exact (egbFixedChargeAGibbsCollisionExcess_total_bound n β E).trans
      (mul_le_mul_of_nonneg_right h (egbFixedChargeAGibbsCollisionExcess_nonneg n 0 β E))

end
end GaloisForLFunctions.HTGeometry
