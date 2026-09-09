import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionExcess

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Centered Gibbs populations inherit the exact residual factor in two transitions. -/
theorem egbFixedChargeAGibbsCentered_refresh (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 2) β E i - ((2 : ℝ) ^ (n + 3))⁻¹ =
      (5 / 6) * (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal
        (fun j => egbFixedChargeAGibbsMarkovPopulation n m β E j - ((2 : ℝ) ^ (n + 3))⁻¹) i := by
  rw [egbFixedChargeAGibbsMarkovPopulation_refresh,
    egbFixedChargeACriticalMarkovRefresh_center]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  dsimp only
  field_simp
  <;> ring

/-- The exact uniform refresh supplies a universal two-step contraction of collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_two_step (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 2) β E ≤
      (25 / 36) * egbFixedChargeAGibbsCollisionExcess n m β E := by
  have h := egbFixedChargeACriticalMarkovRefresh_sum_sq_le n
    (fun j => egbFixedChargeAGibbsMarkovPopulation n m β E j - ((2 : ℝ) ^ (n + 3))⁻¹)
  calc
    egbFixedChargeAGibbsCollisionExcess n (m + 2) β E =
        (25 / 36) * ∑ i, ((egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal
          (fun j => egbFixedChargeAGibbsMarkovPopulation n m β E j - ((2 : ℝ) ^ (n + 3))⁻¹) i) ^ 2 := by
      simp only [egbFixedChargeAGibbsCollisionExcess, egbFixedChargeAGibbsCentered_refresh, mul_pow]
      rw [show (5 / 6 : ℝ) ^ 2 = 25 / 36 by norm_num, Finset.mul_sum]
    _ ≤ (25 / 36) * egbFixedChargeAGibbsCollisionExcess n m β E :=
      mul_le_mul_of_nonneg_left h (by norm_num)

/-- The collision excess has an explicit geometric bound at every even time. -/
theorem egbFixedChargeAGibbsCollisionExcess_even_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (2 * m) β E ≤
      (25 / 36 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      calc
        egbFixedChargeAGibbsCollisionExcess n (2 * m + 2) β E ≤
            (25 / 36) * egbFixedChargeAGibbsCollisionExcess n (2 * m) β E :=
          egbFixedChargeAGibbsCollisionExcess_two_step n (2 * m) β E
        _ ≤ (25 / 36) * ((25 / 36 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ (25 / 36 : ℝ) m]; ring

/-- Odd-time excess obeys the same bound, with the extra transition available for free. -/
theorem egbFixedChargeAGibbsCollisionExcess_odd_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (2 * m + 1) β E ≤
      (25 / 36 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E :=
  (egbFixedChargeAGibbsCollisionExcess_antitone n β E (by omega)).trans
    (egbFixedChargeAGibbsCollisionExcess_even_bound n m β E)

end
end GaloisForLFunctions.HTGeometry
