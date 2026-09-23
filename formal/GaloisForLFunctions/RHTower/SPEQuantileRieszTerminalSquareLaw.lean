import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalErrorGate
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCompletedEndpointLaw

/-!
# SP-E terminal Riesz square law

The terminal scalar Riesz readout is exactly a positive cubic factor times the square of the
signed completed error/atom displacement.  Thus it is coercive for that displacement, while its
scalarization necessarily forgets its sign.  This isolates the information that a collective
signed-current argument must retain before terminal readout.
-/

namespace RHTower

noncomputable section

/-- Signed discrepancy between the completed-error/atom channel and its terminal threshold. -/
def speQuantileRieszTerminalErrorDisplacement (K : ℕ) : ℝ :=
  criticalMellinCompletedError (Real.log ((K : ℝ) + 3)) +
    criticalMellinAtomWeight (K + 3) -
      2 * (1 - Real.exp (-(Real.log ((K : ℝ) + 3) / 2)))

/-- At the physical parabolic wall, Riesz readout is an exact signed-mismatch square. -/
theorem speQuantileRieszParabolicReadout_moment_at_physicalWall_eq_square_factor
    (M : ℕ) (a : ℝ) :
    speQuantileRieszParabolicReadout M
        (ccmParabolicMoment a (2 * Real.sqrt (M : ℝ))) =
      (2 * Real.sqrt (M : ℝ) - a) ^ (2 : ℕ) *
        (Real.sqrt (M : ℝ) + a) / 6 := by
  rw [speQuantileRieszParabolicReadout_moment]
  unfold speQuantileRieszMassAntiderivative
  ring

/-- Terminal completed readout is an exact square in its physical polar mismatch. -/
theorem speQuantileRieszTerminalReadout_eq_physicalMismatch_square_factor (K : ℕ) :
    speQuantileRieszParabolicReadout (K + 3)
        (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) =
      (2 * Real.sqrt ((K + 3 : ℕ) : ℝ) -
        ccmActualHeadQuantilePolarCoordinate (K + 3)) ^ (2 : ℕ) *
          (Real.sqrt ((K + 3 : ℕ) : ℝ) +
            ccmActualHeadQuantilePolarCoordinate (K + 3)) / 6 := by
  unfold ccmActualHeadQuantileParabolicTerminal
  have hclock : Real.log ((K : ℝ) + 3) =
      Real.log ((K + 3 : ℕ) : ℝ) := by norm_num
  rw [hclock, ccmActualHeadPolarMassCoordinate_log_nat (K + 3) (by omega)]
  exact speQuantileRieszParabolicReadout_moment_at_physicalWall_eq_square_factor _ _

/-- The signed completed error/atom discrepancy is the terminal physical polar mismatch. -/
theorem speQuantileRieszTerminalErrorDisplacement_eq_physicalMismatch (K : ℕ) :
    speQuantileRieszTerminalErrorDisplacement K =
      2 * Real.sqrt ((K + 3 : ℕ) : ℝ) -
        ccmActualHeadQuantilePolarCoordinate (K + 3) := by
  have h :=
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero_eq_threshold_sub_error_sub_atom K
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero] at h
  have hclock : Real.log ((K : ℝ) + 3) =
      Real.log ((K + 3 : ℕ) : ℝ) := by norm_num
  rw [hclock, ccmActualHeadPolarMassCoordinate_log_nat (K + 3) (by omega)] at h
  unfold speQuantileRieszTerminalErrorDisplacement
  rw [hclock]
  linarith

/-- Terminal completed readout is an exact square in the signed error/atom discrepancy. -/
theorem speQuantileRieszTerminalReadout_eq_errorDisplacement_square_factor (K : ℕ) :
    speQuantileRieszParabolicReadout (K + 3)
        (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) =
      speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) *
        (3 * Real.sqrt ((K + 3 : ℕ) : ℝ) -
          speQuantileRieszTerminalErrorDisplacement K) / 6 := by
  rw [speQuantileRieszTerminalReadout_eq_physicalMismatch_square_factor]
  rw [speQuantileRieszTerminalErrorDisplacement_eq_physicalMismatch]
  ring

/-- Terminal completed scalar Riesz readout is nonnegative. -/
theorem speQuantileRieszTerminalReadout_nonneg (K : ℕ) :
    0 ≤ speQuantileRieszParabolicReadout (K + 3)
        (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) := by
  rw [speQuantileRieszTerminalReadout_eq_physicalMismatch_square_factor]
  have hq : 0 < ccmActualHeadQuantilePolarCoordinate (K + 3) := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  positivity

/-- Terminal scalar readout coercively controls the square of the signed error/atom discrepancy. -/
theorem speQuantileRieszTerminalErrorDisplacement_sq_le_terminalReadout (K : ℕ) :
    Real.sqrt ((K + 3 : ℕ) : ℝ) / 6 *
        speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) ≤
      speQuantileRieszParabolicReadout (K + 3)
        (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) := by
  rw [speQuantileRieszTerminalReadout_eq_errorDisplacement_square_factor]
  have hq : 0 ≤ ccmActualHeadQuantilePolarCoordinate (K + 3) := by
    unfold ccmActualHeadQuantilePolarCoordinate
    positivity
  have hfactor : Real.sqrt ((K + 3 : ℕ) : ℝ) ≤
      3 * Real.sqrt ((K + 3 : ℕ) : ℝ) -
        speQuantileRieszTerminalErrorDisplacement K := by
    rw [speQuantileRieszTerminalErrorDisplacement_eq_physicalMismatch]
    linarith
  have hsq : 0 ≤ speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) := sq_nonneg _
  nlinarith

/-- The terminal scalar readout vanishes exactly when the signed error/atom discrepancy vanishes. -/
theorem speQuantileRieszTerminalReadout_eq_zero_iff_errorDisplacement_eq_zero (K : ℕ) :
    speQuantileRieszParabolicReadout (K + 3)
        (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) = 0 ↔
      speQuantileRieszTerminalErrorDisplacement K = 0 := by
  constructor
  · intro hzero
    have hlower := speQuantileRieszTerminalErrorDisplacement_sq_le_terminalReadout K
    have hroot : 0 < Real.sqrt ((K + 3 : ℕ) : ℝ) / 6 := by positivity
    have hsq : 0 ≤ speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) := sq_nonneg _
    have hmul_nonneg : 0 ≤ Real.sqrt ((K + 3 : ℕ) : ℝ) / 6 *
        speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) :=
      mul_nonneg (le_of_lt hroot) hsq
    have hmul : Real.sqrt ((K + 3 : ℕ) : ℝ) / 6 *
        speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmul with hfactor | hsq_zero
    · exact (ne_of_gt hroot hfactor).elim
    · nlinarith
  · intro hzero
    rw [speQuantileRieszTerminalReadout_eq_errorDisplacement_square_factor, hzero]
    norm_num

end

end RHTower
