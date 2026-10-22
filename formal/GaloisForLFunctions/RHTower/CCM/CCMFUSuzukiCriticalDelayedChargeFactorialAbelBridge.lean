import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalDelayedChargeFactorialBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation

/-!
# Abel factorization of the literal critical CCM--FU wall charge

The factorial bridge identifies the finite coefficient prefix.  Finite Abel summation then
expresses the entire square-root delayed wall charge as a positive-increment functional of that
same signed Chebyshev--factorial prefix.  This is an exact source identity; it supplies no bound
on the resulting functional.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal coefficient of the critical delayed prime--polar charge. -/
def ccmFUSuzukiCriticalPrimePolarCoefficient (j : ℕ) : ℝ :=
  ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j

/-- Literal finite prefix of the critical delayed prime--polar coefficients. -/
def ccmFUSuzukiCriticalPrimePolarPrefix (N : ℕ) : ℝ :=
  deningerPartialSum ccmFUSuzukiCriticalPrimePolarCoefficient N

/-- The exact Chebyshev--factorial form of the literal critical coefficient prefix. -/
def ccmFUSuzukiCriticalChebyshevFactorialPrefix (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt (j + 3)) -
    (((N + 3 : ℕ) : ℝ) * Real.log ((N + 3 : ℕ) : ℝ) -
      Real.log (((N + 2).factorial : ℕ) : ℝ) - 2 * Real.log 2)

/-- The literal critical coefficient prefix is exactly its Chebyshev--factorial discrepancy. -/
theorem ccmFUSuzuki_criticalPrimePolarPrefix_eq_chebyshevFactorial
    (N : ℕ) :
    ccmFUSuzukiCriticalPrimePolarPrefix N =
      ccmFUSuzukiCriticalChebyshevFactorialPrefix N := by
  unfold ccmFUSuzukiCriticalPrimePolarPrefix
    ccmFUSuzukiCriticalPrimePolarCoefficient
    ccmFUSuzukiCriticalChebyshevFactorialPrefix deningerPartialSum
  simpa [Nat.add_assoc] using
    ccmFUSuzuki_criticalPrimePolarCumulative_eq_chebyshevFactorial (N + 1)

/-- Finite Abel form of the literal square-root-delayed wall charge. -/
theorem ccmFUSuzuki_criticalWallCharge_eq_abelPrefix
    (N : ℕ) (Y : ℝ) :
    (∑ j ∈ Finset.range (N + 1),
      ccmFUSuzukiCriticalPrimePolarCoefficient j *
        (Y - Real.sqrt ((j + 3 : ℕ) : ℝ))) =
      ccmFUSuzukiCriticalPrimePolarPrefix N *
        (Y - Real.sqrt ((N + 3 : ℕ) : ℝ)) +
      ∑ j ∈ Finset.range N,
        ccmFUSuzukiCriticalPrimePolarPrefix j *
          (Real.sqrt ((j + 4 : ℕ) : ℝ) - Real.sqrt ((j + 3 : ℕ) : ℝ)) := by
  rw [deningerAbelSummation]
  unfold ccmFUSuzukiCriticalPrimePolarPrefix
  apply congrArg (fun z : ℝ => deningerPartialSum ccmFUSuzukiCriticalPrimePolarCoefficient N *
    (Y - Real.sqrt ((N + 3 : ℕ) : ℝ)) + z)
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Exact source-faithful Abel factorization of the delayed wall charge. -/
theorem ccmFUSuzuki_criticalWallCharge_eq_abelChebyshevFactorialPrefix
    (N : ℕ) (Y : ℝ) :
    (∑ j ∈ Finset.range (N + 1),
      ccmFUSuzukiCriticalPrimePolarCoefficient j *
        (Y - Real.sqrt ((j + 3 : ℕ) : ℝ))) =
      ccmFUSuzukiCriticalChebyshevFactorialPrefix N *
        (Y - Real.sqrt ((N + 3 : ℕ) : ℝ)) +
      ∑ j ∈ Finset.range N,
        ccmFUSuzukiCriticalChebyshevFactorialPrefix j *
          (Real.sqrt ((j + 4 : ℕ) : ℝ) - Real.sqrt ((j + 3 : ℕ) : ℝ)) := by
  rw [ccmFUSuzuki_criticalWallCharge_eq_abelPrefix,
    ccmFUSuzuki_criticalPrimePolarPrefix_eq_chebyshevFactorial]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ccmFUSuzuki_criticalPrimePolarPrefix_eq_chebyshevFactorial]

end

end RHTower
