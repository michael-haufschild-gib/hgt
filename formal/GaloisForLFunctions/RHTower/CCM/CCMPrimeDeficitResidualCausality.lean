import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitResidualReflection
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitResidualPrimeForce

/-!
# Delayed entry of the actual prime correction

Residual counts begin at `m+1`, and prime forcing begins at `2(m+1)`.
Their reflected interaction therefore starts at radius `2(m+1)^2`.
Below that radius the complete defect is the exponential reflection
pairing, for arbitrary cutoffs without the old `3k <= m` restriction.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

theorem ccmPrimeDeficitResidualCountProfile_eq_zero_before_entry (m U : ℕ)
    {t : ℝ} (ht : ⌊Real.exp t⌋₊ ≤ m) :
    ccmPrimeDeficitResidualCountProfile m U t = 0 := by
  rw [ccmPrimeDeficitResidualCountProfile, logarithmicFiniteEntryProfile_eq_min_prefix]
  apply Finset.sum_eq_zero
  intro n hn
  have hnm : n ≤ m := ((Finset.mem_Icc.mp hn).2.trans (min_le_right _ _)).trans ht
  rw [ccmPrimeDeficitResidualCoeff_of_le hnm, zero_mul]

theorem ccmPrimeDeficitResidualLogProfile_eq_zero_before_entry (m U : ℕ)
    {t : ℝ} (ht : ⌊Real.exp t⌋₊ < 2 * (m + 1)) :
    logarithmicFiniteEntryProfile (ccmPrimeDeficitResidualLogCoeff m) U (fun _ => 1) t = 0 := by
  rw [logarithmicFiniteEntryProfile_eq_min_prefix]
  apply Finset.sum_eq_zero
  intro n hn
  have hnm : n < 2 * (m + 1) :=
    ((Finset.mem_Icc.mp hn).2.trans (min_le_right _ _)).trans_lt ht
  rw [ccmPrimeDeficitResidualLogCoeff_of_lt_twice hnm, zero_mul]

/-- Multiplicative support, including all arithmetic signs, removes the
entire logarithmic prime correction below its first product entry. -/
theorem logarithmicWeightedDilation_residual_prime_pair_eq_zero (m : ℕ)
    {T : ℝ} (hT : ⌊Real.exp T⌋₊ < 2 * (m + 1) ^ 2) :
    logarithmicWeightedDilation (ccmPrimeDeficitResidualLogCoeff m)
      (logarithmicWeightedDilation (ccmPrimeDeficitResidualCoeff m) logarithmicLinearRamp) T = 0 := by
  rw [logarithmicWeightedDilation_comp]
  unfold logarithmicWeightedDilation
  apply Finset.sum_eq_zero
  intro n hn
  have hnT : n < 2 * (m + 1) ^ 2 := (Finset.mem_Icc.mp hn).2.trans_lt hT
  have hz : (∑ ab ∈ n.divisorsAntidiagonal,
      ccmPrimeDeficitResidualLogCoeff m ab.1 * ccmPrimeDeficitResidualCoeff m ab.2) = 0 := by
    apply Finset.sum_eq_zero
    intro ab hab
    by_cases ha : ab.1 < 2 * (m + 1)
    · rw [ccmPrimeDeficitResidualLogCoeff_of_lt_twice ha, zero_mul]
    · have hb : ab.2 ≤ m := by
        by_contra hb
        have hprod : 2 * (m + 1) ^ 2 ≤ n := by
          calc
            _ = (2 * (m + 1)) * (m + 1) := by ring
            _ ≤ ab.1 * ab.2 := Nat.mul_le_mul (Nat.le_of_not_gt ha) (by omega)
            _ = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
        omega
      rw [ccmPrimeDeficitResidualCoeff_of_le hb, mul_zero]
  dsimp only
  rw [hz, zero_mul]

/-- Until the prime correction arrives, the global reflection formula
reduces to its exponential component with the actual residual coefficients. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_exponential_reflection_before_prime_entry
    (m : ℕ) {T : ℝ} (h0 : 0 ≤ T) (hT : ⌊Real.exp T⌋₊ < 2 * (m + 1) ^ 2) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      ∫ s in (0 : ℝ)..T,
        logarithmicFiniteEntryProfile (ccmPrimeDeficitResidualCoeff m) ⌊Real.exp T⌋₊ Real.exp s *
          ccmPrimeDeficitResidualCountProfile m ⌊Real.exp T⌋₊ (T - s) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_residual_pair m h0,
    logarithmicWeightedDilation_residual_prime_pair_eq_zero m hT, sub_zero,
    logarithmicWeightedDilation_pair_exponentialRamp_eq_reflection]
  rfl

end RHTower
