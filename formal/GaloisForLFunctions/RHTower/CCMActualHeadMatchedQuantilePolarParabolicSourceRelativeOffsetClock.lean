import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCanonicalClockAllHeadNoGo

/-!
# Source-relative offset clock for literal completed parabolic current

Canonical integer clock has forced unbounded jumps at zero von-Mangoldt atoms. Moving physical
endpoint to literal outgoing quantile wall avoids those jumps, but wall terminal vanishes and
loses second codiagonal coordinate. This module uses a fixed nonzero offset from literal quantile
wall: it is stationary at zero atoms while retaining nonzero terminal mass lever.

This is clock infrastructure only: no bound on retained signed source current or RH consequence.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Literal completed source current at fixed physical offset from actual outgoing quantile wall. -/
def ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
    (u : ℝ) (K : ℕ) : ℝ :=
  ccmParabolicPairing
    (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
      (ccmOutgoingPrimeQuantileBoundary (K + 3) + u))
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K
      (ccmOutgoingPrimeQuantileBoundary (K + 3) + u))

/-- Literal quantile wall does not move across zero von-Mangoldt atom. -/
theorem ccmOutgoingPrimeQuantileBoundary_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmOutgoingPrimeQuantileBoundary (K + 4) =
      ccmOutgoingPrimeQuantileBoundary (K + 3) := by
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [ccmOutgoingPrimeCumulative_succ,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring_nf

/-- Quantile polar endpoint is stationary across zero von-Mangoldt atom. -/
theorem ccmActualHeadQuantilePolarCoordinate_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadQuantilePolarCoordinate (K + 4) =
      ccmActualHeadQuantilePolarCoordinate (K + 3) := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmOutgoingPrimeCumulative_succ,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring_nf

/-- Finite quantile carrier, like matched carrier, is stationary across zero atom. -/
theorem ccmActualHeadQuantileParabolicAggregate_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadQuantileParabolicAggregate (K + 1) =
      ccmActualHeadQuantileParabolicAggregate K := by
  rw [ccmActualHeadQuantileParabolicAggregate_eq_moment,
    ccmActualHeadQuantileParabolicAggregate_eq_moment,
    ccmActualHeadQuantilePolarCoordinate_succ_eq_of_not_isPrimePow K hK]

/-- Literal terminal is stationary when finite endpoint and source-relative clock are stationary. -/
theorem ccmActualHeadQuantileParabolicTerminal_succ_eq_of_not_isPrimePow
    (u : ℝ) (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadQuantileParabolicTerminal (K + 1)
        (ccmOutgoingPrimeQuantileBoundary (K + 4) + u) =
      ccmActualHeadQuantileParabolicTerminal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3) + u) := by
  unfold ccmActualHeadQuantileParabolicTerminal
  rw [ccmOutgoingPrimeQuantileBoundary_succ_eq_of_not_isPrimePow K hK,
    ccmActualHeadQuantilePolarCoordinate_succ_eq_of_not_isPrimePow K hK]

/-- **Zero-atom drift elimination.** Source-relative offset current is exactly stationary at
every non-prime-power admission, eliminating canonical endpoint-quartic drift. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_succ_eq_of_not_isPrimePow
    (u : ℝ) (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u (K + 1) =
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary
    ccmActualHeadCompletedQuantileParabolicAggregate
  rw [ccmActualHeadQuantileParabolicTerminal_succ_eq_of_not_isPrimePow u K hK,
    ccmActualHeadMatchedParabolicAggregate_succ_eq_of_not_isPrimePow K hK,
    ccmActualHeadQuantileParabolicAggregate_succ_eq_of_not_isPrimePow K hK]

/-- Nonzero offset retains terminal mass lever, unlike exact-quantile-wall degeneration. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolic_offset_zero_ne_zero
    {u : ℝ} (hu : u ≠ 0) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3) + u) 0 ≠ 0 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero,
    ← ccmActualHeadPolarMassCoordinate_quantileBoundary (K + 3)]
  intro hzero
  unfold ccmActualHeadPolarMassCoordinate at hzero
  have hexp : Real.exp ((ccmOutgoingPrimeQuantileBoundary (K + 3) + u) / 2) =
      Real.exp (ccmOutgoingPrimeQuantileBoundary (K + 3) / 2) := by
    linarith
  have harg : (ccmOutgoingPrimeQuantileBoundary (K + 3) + u) / 2 =
      ccmOutgoingPrimeQuantileBoundary (K + 3) / 2 := Real.exp_injective hexp
  apply hu
  linarith [harg]

end RHTower
