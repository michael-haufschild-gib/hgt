import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTwoRateEquilibrium

/-!
# Exact collision budgets and refined information budgets

The two retained decay rates of the arXiv:2609.00025 critical thermal kernel
can be summed separately. This records exactly how the initial spectral
energies contribute to the entire collision history.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem geometric_tail_sum (r A : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun m : ℕ => r ^ (m + 1) * A) (r / (1 - r) * A) := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right (r * A)
  have he : (fun m : ℕ => r ^ (m + 1) * A) = (fun m => r ^ m * (r * A)) := by
    funext m
    rw [pow_succ r m]
    ring
  have hv : r / (1 - r) * A = (1 - r)⁻¹ * (r * A) := by ring
  rw [he, hv]
  exact h

/-- The complete positive-time collision tail has an exact slow-plus-fast sum. -/
theorem egbFixedChargeAGibbsCollisionExcess_two_rate_tail_hasSum (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
      ((4 / 5 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 35 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
  have hA := geometric_tail_sum (4 / 9) (egbFixedChargeAGibbsSlowModeEnergy n β E)
    (by norm_num) (by norm_num)
  have hB := geometric_tail_sum (1 / 36) (egbFixedChargeAGibbsFastModeEnergy n β E)
    (by norm_num) (by norm_num)
  norm_num at hA hB
  have he : (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) =
      (fun m => (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) :=
    funext (fun m => egbFixedChargeAGibbsCollisionExcess_two_rate n m β E)
  rw [he]
  simpa only [Pi.add_def] using hA.add hB

/-- The total collision budget separates the initial value and the two surviving spectral tails. -/
theorem egbFixedChargeAGibbsCollisionExcess_total_exact (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsCollisionExcess n m β E) =
      egbFixedChargeAGibbsCollisionExcess n 0 β E +
        (4 / 5 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
          (1 / 35 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [(egbFixedChargeAGibbsCollisionExcess_summable n β E).tsum_eq_zero_add,
    (egbFixedChargeAGibbsCollisionExcess_two_rate_tail_hasSum n β E).tsum_eq]
  ring

/-- Retained spectral energies bound all relative information remaining after the first transition. -/
theorem egbFixedChargeAGibbsEntropyDeficit_two_rate_tail_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) ≤
      (2 : ℝ) ^ (n + 3) *
        ((4 / 5 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
          (1 / 35 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
  have hs : Summable (fun m : ℕ => egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) :=
    (summable_nat_add_iff 1).mpr (egbFixedChargeAGibbsEntropyDeficit_summable n β E)
  exact hasSum_le (fun m => egbFixedChargeAGibbsEntropyDeficit_collision_upper n (m + 1) β E)
    hs.hasSum ((egbFixedChargeAGibbsCollisionExcess_two_rate_tail_hasSum n β E).mul_left
      ((2 : ℝ) ^ (n + 3)))

/-- The complete relative-information budget includes its exact initial value and a spectral tail bound. -/
theorem egbFixedChargeAGibbsEntropyDeficit_two_rate_total_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑' m : ℕ, egbFixedChargeAGibbsEntropyDeficit n m β E) ≤
      egbFixedChargeAGibbsEntropyDeficit n 0 β E + (2 : ℝ) ^ (n + 3) *
        ((4 / 5 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
          (1 / 35 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) := by
  rw [(egbFixedChargeAGibbsEntropyDeficit_summable n β E).tsum_eq_zero_add]
  linarith [egbFixedChargeAGibbsEntropyDeficit_two_rate_tail_bound n β E]

end
end GaloisForLFunctions.HTGeometry
