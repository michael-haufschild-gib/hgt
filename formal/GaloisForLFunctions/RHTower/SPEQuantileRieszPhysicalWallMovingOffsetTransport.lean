import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetIncrement

/-!
# Moving-offset transport at the physical SP-E wall

The physical wall `log (K + 3)` is not a fixed offset from the literal outgoing quantile wall.
Its unique source-relative offset moves.  This module identifies the physical completed current
with the source-relative current at that moving offset, and computes the transport that this
motion contributes.

At every zero von-Mangoldt atom, the fixed-offset source current is stationary, but the physical
offset increases strictly.  The resulting offset transport is exactly the negative canonical
endpoint-quartic jump and has linearly growing magnitude.  Hence a fixed-offset clock cannot be
upgraded to the physical wall by an asymptotically negligible correction.  Any viable SP-E
cofinal producer must cancel this dynamic transport jointly with the full nonlocal signed source
ledger; no sign, atom, terminal coordinate, or gauge term is discarded here.
-/

noncomputable section

namespace RHTower

/-- The unique offset from the outgoing quantile wall to the physical SP-E time wall. -/
def speQuantileRieszPhysicalWallOffset (K : ℕ) : ℝ :=
  Real.log (K + 3) - ccmOutgoingPrimeQuantileBoundary (K + 3)

/-- **Physical-wall identification.**  The literal physical completed current is the existing
source-relative current evaluated at its moving physical offset. -/
theorem speQuantileRieszPhysicalWallOffset_current_eq_canonical
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
        (speQuantileRieszPhysicalWallOffset K) K =
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
    speQuantileRieszPhysicalWallOffset
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent
  have htime :
      ccmOutgoingPrimeQuantileBoundary (K + 3) +
          (Real.log (K + 3) - ccmOutgoingPrimeQuantileBoundary (K + 3)) =
        Real.log (K + 3) := by ring
  rw [htime]

/-- At a zero atom, quantile stationarity makes the physical offset move by exactly the logarithmic
integer-clock increment. -/
theorem speQuantileRieszPhysicalWallOffset_succ_sub_eq_logIncrement_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszPhysicalWallOffset (K + 1) -
        speQuantileRieszPhysicalWallOffset K =
      Real.log (K + 4) - Real.log (K + 3) := by
  unfold speQuantileRieszPhysicalWallOffset
  rw [ccmOutgoingPrimeQuantileBoundary_succ_eq_of_not_isPrimePow K hK]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The physical wall offset is strictly increasing at every zero von-Mangoldt atom. -/
theorem speQuantileRieszPhysicalWallOffset_strictMonoAt_zeroAtom
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszPhysicalWallOffset K <
      speQuantileRieszPhysicalWallOffset (K + 1) := by
  have hlog : Real.log (K + 3) < Real.log (K + 4) :=
    Real.strictMonoOn_log (by simp; positivity) (by simp; positivity) (by norm_num)
  have hdiff : 0 < speQuantileRieszPhysicalWallOffset (K + 1) -
      speQuantileRieszPhysicalWallOffset K := by
    rw [speQuantileRieszPhysicalWallOffset_succ_sub_eq_logIncrement_of_not_isPrimePow K hK]
    exact sub_pos.mpr hlog
  exact sub_pos.mp hdiff

/-- Exact change under two source-relative offsets at one fixed finite head.  It is the endpoint
quartic transport and contains no matched-source approximation. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_offsetTransport
    (u v : ℝ) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent v K -
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u K =
      ((Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ 4 -
        (Real.exp (v / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ 4) / 12 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic]
  ring

/-- **Dynamic transport identity.**  At a zero atom, the moving physical offset contributes
exactly the negative canonical endpoint-quartic increment. -/
theorem speQuantileRieszPhysicalWall_dynamicOffset_transport_eq_endpointQuartic_sub_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ((Real.exp (speQuantileRieszPhysicalWallOffset K / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4 -
        (Real.exp (speQuantileRieszPhysicalWallOffset (K + 1) / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4) / 12 =
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) := by
  calc
    _ = ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
          (speQuantileRieszPhysicalWallOffset (K + 1)) (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
          (speQuantileRieszPhysicalWallOffset K) (K + 1) := by
      symm
      exact ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_offsetTransport
        (speQuantileRieszPhysicalWallOffset K)
        (speQuantileRieszPhysicalWallOffset (K + 1)) (K + 1)
    _ = ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
          (speQuantileRieszPhysicalWallOffset (K + 1)) (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
          (speQuantileRieszPhysicalWallOffset K) K := by
      rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_succ_eq_of_not_isPrimePow
        (speQuantileRieszPhysicalWallOffset K) K hK]
    _ = _ := by
      rw [speQuantileRieszPhysicalWallOffset_current_eq_canonical,
        speQuantileRieszPhysicalWallOffset_current_eq_canonical]
      exact ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_succ_sub_eq_endpointQuartic_sub_of_not_isPrimePow K hK

/-- **Quantitative moving-clock obstruction.**  At every zero atom, the source-relative transport
needed to recover the physical wall is negative with at least linear magnitude.  It is therefore
not a small gauge correction to the stationary source-relative update. -/
theorem speQuantileRieszPhysicalWall_dynamicOffset_transport_le_neg_linear_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ((Real.exp (speQuantileRieszPhysicalWallOffset K / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4 -
        (Real.exp (speQuantileRieszPhysicalWallOffset (K + 1) / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4) / 12 ≤
      -(2 / 9 : ℝ) * (K + 3) := by
  have hKone : 1 ≤ K := by
    by_contra hnot
    have hzero : K = 0 := by omega
    subst K
    exact (hK (by simpa using Nat.prime_three.isPrimePow)).elim
  rw [speQuantileRieszPhysicalWall_dynamicOffset_transport_eq_endpointQuartic_sub_of_not_isPrimePow K hK]
  have hendpoint :=
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic_succ_sub_lower_at_head K hKone
  linarith

end RHTower
