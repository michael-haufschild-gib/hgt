import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalDelayedChargeTransport

/-!
# Factorial cancellation in the literal critical CCM--FU charge

The cumulative coefficients of the critical delayed charge are not separate prime and polar
envelopes.  Their polar primitive telescopes exactly to a factorial logarithm.  Hence the
unweighted cumulative charge is a literal Chebyshev--factorial discrepancy.  The surviving
square-root-weighted part of the delayed charge is deliberately not estimated here.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact factorial telescope for the polar coefficients of the critical FU charge. -/
theorem ccmFUSuzuki_weightedLogRatio_sum_eq_factorial
    (M : ℕ) :
    (∑ j ∈ Finset.range M,
      ((j + 3 : ℕ) : ℝ) *
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) =
      ((M + 2 : ℕ) : ℝ) * Real.log ((M + 2 : ℕ) : ℝ) -
        Real.log (((M + 1).factorial : ℕ) : ℝ) - 2 * Real.log 2 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hM2 : ((M + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfact : (((M + 2).factorial : ℕ) : ℝ) =
        ((M + 2 : ℕ) : ℝ) * (((M + 1).factorial : ℕ) : ℝ) := by
      norm_cast
    have hfactne : (((M + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hfact, Real.log_mul hM2 hfactne]
    push_cast
    ring

/-- Exact Chebyshev--factorial form of the unweighted literal critical delayed-charge prefix. -/
theorem ccmFUSuzuki_criticalPrimePolarCumulative_eq_chebyshevFactorial
    (M : ℕ) :
    (∑ j ∈ Finset.range M,
      ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) =
      (∑ j ∈ Finset.range M, ArithmeticFunction.vonMangoldt (j + 3)) -
        (((M + 2 : ℕ) : ℝ) * Real.log ((M + 2 : ℕ) : ℝ) -
          Real.log (((M + 1).factorial : ℕ) : ℝ) - 2 * Real.log 2) := by
  have hterm (j : ℕ) :
      ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j =
        ArithmeticFunction.vonMangoldt (j + 3) -
          ((j + 3 : ℕ) : ℝ) *
            (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) := by
    unfold ccmFUSuzukiCriticalPrimePolarIncrement
    have hj : ((j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hj]
  calc
    (∑ j ∈ Finset.range M,
        ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) =
      ∑ j ∈ Finset.range M,
        (ArithmeticFunction.vonMangoldt (j + 3) -
          ((j + 3 : ℕ) : ℝ) *
            (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        ccmFUSuzuki_weightedLogRatio_sum_eq_factorial]

end

end RHTower
