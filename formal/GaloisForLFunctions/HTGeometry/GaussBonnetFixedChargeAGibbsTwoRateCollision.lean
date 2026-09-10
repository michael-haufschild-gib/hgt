import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsMomentEnergy

/-!
# The exact two-rate collision law

The five Fourier modes of the critical thermal kernel from arXiv:2609.00025
split into one stationary mode, two slow modes, and two fast modes. For every
Gibbs input, collision excess at positive time is the sum of two geometric terms.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Energy stored in the two slow nonconstant Fourier modes. -/
def egbFixedChargeAGibbsSlowModeEnergy (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ‖egbFixedChargeAGibbsFourierMoment n β E 1‖ ^ 2 +
    ‖egbFixedChargeAGibbsFourierMoment n β E 4‖ ^ 2

/-- Energy stored in the two fast nonconstant Fourier modes. -/
def egbFixedChargeAGibbsFastModeEnergy (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ‖egbFixedChargeAGibbsFourierMoment n β E 2‖ ^ 2 +
    ‖egbFixedChargeAGibbsFourierMoment n β E 3‖ ^ 2

/-- The slow spectral coefficient is nonnegative for every Gibbs landscape. -/
theorem egbFixedChargeAGibbsSlowModeEnergy_nonneg (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsSlowModeEnergy n β E :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The fast spectral coefficient is nonnegative for every Gibbs landscape. -/
theorem egbFixedChargeAGibbsFastModeEnergy_nonneg (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsFastModeEnergy n β E :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem square_geometric (a : ℝ) (k : ℕ) : (a ^ k) ^ 2 = (a ^ 2) ^ k := by
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul]

/-- Every positive-time Gibbs collision excess is an exact slow-plus-fast spectral sum. -/
theorem egbFixedChargeAGibbsCollisionExcess_two_rate (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E =
      (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_identity,
    egbFixedChargeAGibbsMarkovPopulation_spectral_energy]
  simp only [square_geometric]
  norm_num [Fin.sum_univ_succ, egbFixedChargeACriticalMarkovEigenvalues]
  rw [egbFixedChargeAGibbsFourierMoment_zero_sq_norm]
  unfold egbFixedChargeAGibbsSlowModeEnergy egbFixedChargeAGibbsFastModeEnergy
  have h3 : (2 : Fin 4).succ = (3 : Fin 5) := rfl
  have h4 : (2 : Fin 3).succ.succ = (4 : Fin 5) := rfl
  simp only [h3, h4]
  ring

end
end GaloisForLFunctions.HTGeometry
