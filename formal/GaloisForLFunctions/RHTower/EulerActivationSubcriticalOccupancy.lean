import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration

/-!
# The subcritical occupancy sum and the damped Gamma kernel

Above the Euler edge the occupancy probabilities of the diagonal activation law are summable, so
almost surely only finitely many primes are occupied: the source is an honest random finite
integer.  This is the exact complement of the critical divergence.

Summing the Fisher damping identity primewise gives the kernel identity: the Möbius depth kernel
is the Gamma valuation kernel damped by the geometric mean of the two occupancy Fisher
informations.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### Summability of the subcritical occupancy probabilities -/

theorem summable_prime_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) := by
  have hnat : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
    rw [Real.summable_nat_rpow]
    linarith
  exact hnat.subtype _

/-- **Equation `(25)`: above the Euler edge the occupancy probabilities are summable.** -/
theorem summable_subcritical_activationOccupancy {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes =>
      diagonalActivationOccupancyProbability (((p : ℕ) : ℝ) ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_prime_rpow_neg hσ)
  · have hq : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    have hden : (0 : ℝ) < 1 + ((p : ℕ) : ℝ) ^ (-σ) := by linarith
    exact div_nonneg hq hden.le
  · have hq : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    have hden : (1 : ℝ) ≤ 1 + ((p : ℕ) : ℝ) ^ (-σ) := by linarith
    have hdenpos : (0 : ℝ) < 1 + ((p : ℕ) : ℝ) ^ (-σ) := by linarith
    rw [diagonalActivationOccupancyProbability, div_le_iff₀ hdenpos]
    nlinarith

/-! ### The damped Gamma kernel -/

/-- **Equation `(18)`: the Möbius depth kernel is the Fisher-damped Gamma valuation kernel.** -/
theorem tsum_mobiusForwardDifference_mul_eq_dampedGammaKernel (p r : Nat.Primes) :
    (∑' e : ℕ, xiMobiusPrimeSchurForwardDifference p e *
        xiMobiusPrimeSchurForwardDifference r e)
      = xiMobiusPrimeSchurValuationDamping p * xiMobiusPrimeSchurValuationDamping r *
        ∑' e : ℕ, xiTransversePrimeHalfShiftedValuationCoordinate p e *
          xiTransversePrimeHalfShiftedValuationCoordinate r e := by
  have hterm : ∀ e : ℕ,
      xiMobiusPrimeSchurForwardDifference p e * xiMobiusPrimeSchurForwardDifference r e
        = (xiMobiusPrimeSchurValuationDamping p * xiMobiusPrimeSchurValuationDamping r) *
          (xiTransversePrimeHalfShiftedValuationCoordinate p e *
            xiTransversePrimeHalfShiftedValuationCoordinate r e) := by
    intro e
    rw [xiMobiusPrimeSchurForwardDifference_eq_dampedValuation,
      xiMobiusPrimeSchurForwardDifference_eq_dampedValuation]
    ring
  rw [tsum_congr hterm, tsum_mul_left]

/-- The damping product is the geometric mean of the two occupancy Fisher informations. -/
theorem damping_mul_damping_eq_sqrt_fisher_mul (p r : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p * xiMobiusPrimeSchurValuationDamping r
      = Real.sqrt (diagonalActivationOccupancyFisher (xiTransversePrimeApertureDiskNode 1 p) *
          diagonalActivationOccupancyFisher (xiTransversePrimeApertureDiskNode 1 r)) := by
  have hp := xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher p
  have hr := xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher r
  rw [← hp, ← hr, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (xiMobiusPrimeSchurValuationDamping_pos p).le,
    Real.sqrt_sq (xiMobiusPrimeSchurValuationDamping_pos r).le]

/-- **Equation `(18)` in Fisher form.** -/
theorem tsum_mobiusForwardDifference_mul_eq_fisherDampedGammaKernel (p r : Nat.Primes) :
    (∑' e : ℕ, xiMobiusPrimeSchurForwardDifference p e *
        xiMobiusPrimeSchurForwardDifference r e)
      = Real.sqrt (diagonalActivationOccupancyFisher (xiTransversePrimeApertureDiskNode 1 p) *
            diagonalActivationOccupancyFisher (xiTransversePrimeApertureDiskNode 1 r)) *
        ∑' e : ℕ, xiTransversePrimeHalfShiftedValuationCoordinate p e *
          xiTransversePrimeHalfShiftedValuationCoordinate r e := by
  rw [tsum_mobiusForwardDifference_mul_eq_dampedGammaKernel,
    damping_mul_damping_eq_sqrt_fisher_mul]

end

end RHTower
