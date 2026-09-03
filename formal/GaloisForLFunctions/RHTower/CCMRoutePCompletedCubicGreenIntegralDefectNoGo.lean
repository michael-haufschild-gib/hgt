import GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenTailSubunit
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Scalar completion cannot retain the integral unit defect

The completed cubic Green scalar tail is strictly subunit.  The corpus also contains a canonical
prime-mixed, trace-class, unit-trace homotopy defect.  This module tests the most direct possible
fusion: multiply that unit defect by the completed scalar.

The result is trace class and strictly subunit in trace norm, but its trace is the completed scalar
itself and therefore cannot equal either integral unit.  Thus scalar completion cannot be used as
an amplitude renormalization of the integral defect.  Any surviving route needs a genuinely
non-scalar coefficient-faithful short whose source-to-index identification is proved before taking
the trace norm.
-/

open Complex

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- Direct scalar fusion of the completed cubic Green tail with the positive unit wall defect. -/
def ccmRoutePCompletedCubicGreenScaledIntegralDefect :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (ccmRoutePCompletedCubicGreenTail : ℂ) •
    primeHodgeHistoryIntegralNuclearHomotopyDefect 1

theorem ccmRoutePCompletedCubicGreenScaledIntegralDefect_memSchattenClass_one :
    MemSchattenClass 1 ccmRoutePCompletedCubicGreenScaledIntegralDefect := by
  exact memSchattenClass_one_smul
    (primeHodgeHistoryIntegralNuclearHomotopyDefect_memSchattenClass_one 1) _

theorem opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect :
    ContinuousLinearMap.opTrace ccmRoutePCompletedCubicGreenScaledIntegralDefect =
      (ccmRoutePCompletedCubicGreenTail : ℂ) := by
  rw [ccmRoutePCompletedCubicGreenScaledIntegralDefect, opTrace_smul,
    opTrace_primeHodgeHistoryIntegralNuclearHomotopyDefect]
  norm_num

theorem traceNorm_ccmRoutePCompletedCubicGreenScaledIntegralDefect :
    traceNorm PrimeHodgeHistoryHilbert
        ccmRoutePCompletedCubicGreenScaledIntegralDefect =
      |ccmRoutePCompletedCubicGreenTail| := by
  rw [ccmRoutePCompletedCubicGreenScaledIntegralDefect, traceNorm_smul,
    traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect]
  norm_num [Complex.norm_real, Real.norm_eq_abs]

theorem traceNorm_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one :
    traceNorm PrimeHodgeHistoryHilbert
      ccmRoutePCompletedCubicGreenScaledIntegralDefect < 1 := by
  rw [traceNorm_ccmRoutePCompletedCubicGreenScaledIntegralDefect]
  exact abs_ccmRoutePCompletedCubicGreenTail_lt_one

theorem norm_opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one :
    ‖ContinuousLinearMap.opTrace
      ccmRoutePCompletedCubicGreenScaledIntegralDefect‖ < 1 := by
  have hle := norm_opTrace_le_traceNorm
    ccmRoutePCompletedCubicGreenScaledIntegralDefect_memSchattenClass_one
  exact hle.trans_lt
    traceNorm_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one

theorem opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_ne_one :
    ContinuousLinearMap.opTrace
      ccmRoutePCompletedCubicGreenScaledIntegralDefect ≠ 1 := by
  intro h
  have hnorm := norm_opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one
  rw [h] at hnorm
  norm_num at hnorm

theorem opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_ne_neg_one :
    ContinuousLinearMap.opTrace
      ccmRoutePCompletedCubicGreenScaledIntegralDefect ≠ -1 := by
  intro h
  have hnorm := norm_opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one
  rw [h] at hnorm
  norm_num at hnorm

/-- Closed no-go certificate for direct scalar amplitude renormalization. -/
theorem ccmRoutePCompletedCubicGreenScaledIntegralDefect_closed :
    MemSchattenClass 1 ccmRoutePCompletedCubicGreenScaledIntegralDefect ∧
      traceNorm PrimeHodgeHistoryHilbert
        ccmRoutePCompletedCubicGreenScaledIntegralDefect < 1 ∧
      ContinuousLinearMap.opTrace
          ccmRoutePCompletedCubicGreenScaledIntegralDefect =
        (ccmRoutePCompletedCubicGreenTail : ℂ) ∧
      ‖ContinuousLinearMap.opTrace
        ccmRoutePCompletedCubicGreenScaledIntegralDefect‖ < 1 ∧
      ContinuousLinearMap.opTrace
          ccmRoutePCompletedCubicGreenScaledIntegralDefect ≠ 1 ∧
      ContinuousLinearMap.opTrace
          ccmRoutePCompletedCubicGreenScaledIntegralDefect ≠ -1 := by
  exact ⟨ccmRoutePCompletedCubicGreenScaledIntegralDefect_memSchattenClass_one,
    traceNorm_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one,
    opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect,
    norm_opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_lt_one,
    opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_ne_one,
    opTrace_ccmRoutePCompletedCubicGreenScaledIntegralDefect_ne_neg_one⟩

end

end RHTower
