import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFastProfile

/-! # Exact orthogonality of the two retained real harmonics -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Every real transition power is symmetric for the finite Euclidean pairing. -/
theorem egbFixedChargeACriticalMarkov_pairing_symm (n m : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, f i * (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal g i) =
      ∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i * g i := by
  change (∑ i, f i * ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * g j) =
    ∑ i, (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * f j) * g i
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [egbFixedChargeACriticalMarkovMatrix_pow_symm n m j i]
  ring

/-- Distinct exact relaxation eigenvalues force the retained real harmonics to be orthogonal. -/
theorem egbFixedChargeACriticalSlowFast_orthogonal (n : ℕ) :
    ∑ i, egbFixedChargeACriticalSlowProfile n i * egbFixedChargeACriticalFastProfile n i = 0 := by
  have h := egbFixedChargeACriticalMarkov_pairing_symm n 1
    (egbFixedChargeACriticalSlowProfile n) (egbFixedChargeACriticalFastProfile n)
  rw [egbFixedChargeACriticalFastProfile_evolution, egbFixedChargeACriticalSlowProfile_evolution] at h
  have hl : (∑ i, egbFixedChargeACriticalSlowProfile n i *
      ((1 / 6 : ℝ) ^ 1 * egbFixedChargeACriticalFastProfile n i)) =
      (1 / 6 : ℝ) * ∑ i, egbFixedChargeACriticalSlowProfile n i * egbFixedChargeACriticalFastProfile n i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hr : (∑ i, ((2 / 3 : ℝ) ^ 1 * egbFixedChargeACriticalSlowProfile n i) *
      egbFixedChargeACriticalFastProfile n i) =
      (2 / 3 : ℝ) * ∑ i, egbFixedChargeACriticalSlowProfile n i * egbFixedChargeACriticalFastProfile n i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hl, hr] at h
  linarith

/-- The two real harmonics have an exact Pythagorean energy law for every real linear combination. -/
theorem egbFixedChargeACriticalSlowFast_square_sum (n : ℕ) (a b : ℝ) :
    (∑ i, (a * egbFixedChargeACriticalSlowProfile n i + b * egbFixedChargeACriticalFastProfile n i) ^ 2) =
      a ^ 2 * egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n) +
      b ^ 2 * egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n) := by
  have hp (i : Fin (2 ^ (n + 3))) :
      (a * egbFixedChargeACriticalSlowProfile n i + b * egbFixedChargeACriticalFastProfile n i) ^ 2 =
        a ^ 2 * egbFixedChargeACriticalSlowProfile n i ^ 2 +
        b ^ 2 * egbFixedChargeACriticalFastProfile n i ^ 2 +
        (2 * a * b) * (egbFixedChargeACriticalSlowProfile n i * egbFixedChargeACriticalFastProfile n i) := by ring
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    egbFixedChargeACriticalSlowFast_orthogonal, mul_zero, add_zero,
    egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalSlowProfile_centered,
    egbFixedChargeACriticalFastProfile_centered]

end
end GaloisForLFunctions.HTGeometry
