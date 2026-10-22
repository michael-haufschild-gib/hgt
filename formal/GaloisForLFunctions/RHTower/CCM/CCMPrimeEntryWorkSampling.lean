import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitChronologicalWork

/-!
# Work conventions at actual prime jumps

Sampling a fraction `theta` of the way through a prime jump shifts the
signed work by `theta` times the quadratic jump budget. Midpoint sampling
absorbs that budget completely. This changes the decomposition, not the
positive storage or the integrated critical energy needing an upper bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def ccmPrimeEntrySampledWork (theta : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) *
    (ccmLogChebyshevDeficitPrimitive (Real.log n) +
      2 * ((n : ℝ) - Chebyshev.psi n + (1 - theta) * ArithmeticFunction.vonMangoldt n))

def ccmPrimeDeficitSampledWork (theta T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t) +
    2 * ccmLogChebyshevDeficitPrimitive T - ccmPrimeEntrySampledWork theta ⌊Real.exp T⌋₊

theorem ccmPrimeEntrySampledWork_eq_prejump (theta : ℝ) (N : ℕ) :
    ccmPrimeEntrySampledWork theta N = ccmPrimeEntryPrejumpWork N -
      2 * theta * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ) := by
  unfold ccmPrimeEntrySampledWork ccmPrimeEntryPrejumpWork
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem ccmPrimeDeficitSampledWork_eq_chronological (theta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitSampledWork theta T =
      ccmPrimeDeficitChronologicalWork T + theta * ccmPrimeEntryJumpBudget T := by
  rw [ccmPrimeDeficitSampledWork, ccmPrimeEntrySampledWork_eq_prejump,
    ccmPrimeDeficitChronologicalWork, ccmPrimeEntryJumpBudget_eq_sum hT]
  ring

/-- Every sampling convention gives the same complete arithmetic balance. -/
theorem ccmPrimeDeficitSampledWork_balance (theta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCausalStorage T +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
        2 + 2 * ccmPrimeDeficitSampledWork theta T +
          (1 - 2 * theta) * ccmPrimeEntryJumpBudget T := by
  rw [ccmPrimeDeficitChronologicalWork_balance hT,
    ccmPrimeDeficitSampledWork_eq_chronological theta hT]
  ring

/-- At the midpoint the explicit jump budget disappears exactly into the
signed work. This identity supplies no upper estimate for that work. -/
theorem ccmPrimeDeficitMidpointWork_balance {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCausalStorage T +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
        2 + 2 * ccmPrimeDeficitSampledWork (1 / 2) T := by
  have h := ccmPrimeDeficitSampledWork_balance (1 / 2) hT
  rw [show (1 : ℝ) - 2 * (1 / 2) = 0 by ring, zero_mul, add_zero] at h
  exact h

theorem ccmPrimeDeficitMidpointWork_lower {T : ℝ} (hT : 0 ≤ T) :
    -1 ≤ ccmPrimeDeficitSampledWork (1 / 2) T := by
  have h := ccmPrimeDeficitMidpointWork_balance hT
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t :=
    intervalIntegral.integral_nonneg hT (fun t _ => ccmPrimeDeficitCriticalEnergy_nonneg t)
  linarith [ccmPrimeDeficitCausalStorage_nonneg T]

/-- Sampling changes the work by a known quadratic leading term and at
most a linear error. It cannot itself improve the total energy estimate. -/
theorem abs_ccmPrimeDeficitSampledWork_shift_le (theta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitSampledWork theta T - ccmPrimeDeficitChronologicalWork T - theta * T ^ 2| ≤
      |theta| * (80 * T + 50) := by
  rw [ccmPrimeDeficitSampledWork_eq_chronological theta hT]
  calc
    _ = |theta| * |ccmPrimeEntryJumpBudget T - T ^ 2| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_ccmPrimeEntryJumpBudget_sub_sq_le hT) (abs_nonneg theta)

end RHTower
