import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetClock

/-!
# Prime-power update law for the source-relative completed parabolic current

The source-relative offset clock removes every zero-atom update, but its remaining arithmetic
content still has to be kept literal.  This module gives the exact update at an admitted index:
the historical interaction of the actual new matched cell, less the physical endpoint-quartic
increment of the offset quantile carrier.  No sign, asymptotic, or RH premise is introduced.

Thus any cofinal control of this current must control this *signed combined update* at prime
powers.  Neither its matched-cell part nor its endpoint part is a lawful standalone reporter.
-/

noncomputable section

namespace RHTower

/-- Moving a physical endpoint a fixed height `u` from an outgoing quantile wall multiplies its
polar mass coordinate by `exp (u / 2)`. -/
theorem ccmActualHeadPolarMassCoordinate_quantileBoundary_add
    (N : ℕ) (u : ℝ) :
    ccmActualHeadPolarMassCoordinate (ccmOutgoingPrimeQuantileBoundary N + u) =
      Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate N := by
  simp only [ccmActualHeadPolarMassCoordinate, ccmActualHeadQuantilePolarCoordinate]
  rw [show (ccmOutgoingPrimeQuantileBoundary N + u) / 2 =
      ccmOutgoingPrimeQuantileBoundary N / 2 + u / 2 by ring,
    Real.exp_add]
  ring

/-- **Source-relative endpoint law.** The literal offset current is the actual matched aggregate
form less the endpoint quartic at the *rescaled actual quantile mass*. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic
    (u : ℝ) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u K =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        (Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12 := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
  rw [ccmActualHeadMatchedCompletedQuantileParabolic_pairing_sourceBoundary_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadPolarMassCoordinate_quantileBoundary_add,
    ccmActualHeadQuantilePolarCoordinate_two]

/-- **Literal admitted-index update.** A source-relative current update is exactly the interaction
of the historical matched aggregate with the newly admitted actual matched cell, plus that cell's
self-form, minus the rescaled quantile endpoint-quartic increment.  This preserves all
prime--polar cancellation; it does not estimate either signed summand. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_succ_sub_eq_matchedCell_sub_endpointIncrement
    (u : ℝ) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u (K + 1) -
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u K =
      2 * ccmParabolicPairing (ccmActualHeadMatchedParabolicAggregate K)
          (ccmActualHeadMatchedParabolicMoment (K + 3)) +
        ccmParabolicForm (ccmActualHeadMatchedParabolicMoment (K + 3)) -
        ((Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ (4 : ℕ) / 12 -
          (Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (4 : ℕ) / 12) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_eq_matchedForm_sub_endpointQuartic,
    ccmActualHeadMatchedParabolicAggregate_succ,
    ccmParabolicForm_add]
  ring

/-- **Coefficient-faithful source update.** Expanding the physical endpoint increment shows its
three history-dependent terms and the fourth-order diagonal residual exactly.  The latter is
`(1 - exp (u / 2)^(4 : ℕ)) * atomWeight^(4 : ℕ) / 12`; it is retained rather than discarded. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_succ_sub_eq_admittedIndexExpansion
    (u : ℝ) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u (K + 1) -
      ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent u K =
      2 * ccmParabolicPairing (ccmActualHeadMatchedParabolicAggregate K)
          (ccmActualHeadMatchedParabolicMoment (K + 3)) -
        (Real.exp (u / 2) * criticalMellinAtomWeight (K + 3) *
            (Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (3 : ℕ) / 3 +
          Real.exp (u / 2) ^ (2 : ℕ) * criticalMellinAtomWeight (K + 3) ^ (2 : ℕ) *
            (Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) ^ (2 : ℕ) / 2 +
          Real.exp (u / 2) ^ (3 : ℕ) * criticalMellinAtomWeight (K + 3) ^ (3 : ℕ) *
            (Real.exp (u / 2) * ccmActualHeadQuantilePolarCoordinate (K + 3) - 2) / 3) +
        (1 - Real.exp (u / 2) ^ (4 : ℕ)) * criticalMellinAtomWeight (K + 3) ^ (4 : ℕ) / 12 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent_succ_sub_eq_matchedCell_sub_endpointIncrement]
  have hform : ccmParabolicForm (ccmActualHeadMatchedParabolicMoment (K + 3)) =
      criticalMellinAtomWeight (K + 3) ^ (4 : ℕ) / 12 := by
    rw [ccmActualHeadMatchedParabolicMoment, ccmParabolicForm_moment,
      ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
  have hquantile : ccmActualHeadQuantilePolarCoordinate (K + 4) =
      ccmActualHeadQuantilePolarCoordinate (K + 3) + criticalMellinAtomWeight (K + 3) := by
    linarith [ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (K + 3)]
  rw [hform, hquantile]
  ring

/-- The fourth-order diagonal residual of a fixed source-relative offset vanishes exactly at the
degenerate quantile wall.  Thus no nonzero fixed offset can preserve diagonal cancellation by
itself; a surviving producer must cancel this residual jointly with the other signed terms. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffset_diagonalResidual_eq_zero_iff
    (u : ℝ) :
    1 - Real.exp (u / 2) ^ (4 : ℕ) = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hpow : Real.exp (u / 2) ^ (4 : ℕ) = 1 := by linarith
    have hexp : Real.exp (2 * u) = 1 := by
      calc
        Real.exp (2 * u) = Real.exp (4 * (u / 2)) := by congr 1; ring
        _ = Real.exp (u / 2) ^ (4 : ℕ) := by
          convert Real.exp_nat_mul (u / 2) 4 using 1; norm_num
        _ = 1 := hpow
    linarith [(Real.exp_eq_one_iff (2 * u)).mp hexp]
  · rintro rfl
    norm_num

/-- **Fixed-offset incompatibility.** Exact diagonal self-cancellation forces the terminal
mass-lever coordinate to vanish.  Hence a scalar source-relative offset cannot simultaneously
retain the second-coordinate port and preserve diagonal cancellation. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffset_diagonalCancellation_forces_zeroMassLever
    (u : ℝ) (K : ℕ)
    (hdiagonal : 1 - Real.exp (u / 2) ^ (4 : ℕ) = 0) :
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3) + u) 0 = 0 := by
  have hu : u = 0 :=
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffset_diagonalResidual_eq_zero_iff u |>.mp hdiagonal
  subst u
  rw [add_zero, ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero,
    ccmActualHeadPolarMassCoordinate_quantileBoundary]
  ring

/-- Contrapositive form of the fixed-offset incompatibility: any nonzero mass lever necessarily
carries a nonzero fourth-order diagonal residual, which must be cancelled by a genuinely joint
source producer. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffset_nonzeroMassLever_forces_diagonalResidual
    (u : ℝ) (K : ℕ)
    (hlever : ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3) + u) 0 ≠ 0) :
    1 - Real.exp (u / 2) ^ (4 : ℕ) ≠ 0 := by
  intro hdiagonal
  exact hlever
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffset_diagonalCancellation_forces_zeroMassLever
      u K hdiagonal)

end RHTower
