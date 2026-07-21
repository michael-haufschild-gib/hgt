import GaloisForLFunctions.HTGeometry.GlobalToUpperEndDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.ThermalMassClockObservability
import GaloisForLFunctions.RHTower.XiHypertranscendenceChain
import GaloisForLFunctions.RHTower.XiUpperEndHypertranscendence

/-!
# Unconditional hypertranscendence of the completed xi function

The actual upper-end carrier constructed from the completed xi function is the generic
entire-function carrier after rotation by `-I`.  Its upper-end hypertranscendence therefore
descends to global functional hypertranscendence.

This also closes the historical `XiFrequencyCollapse` proposition.  That interface quantifies
over a nonzero algebraic differential relation for xi; unconditional hypertranscendence rules
out the premise, and hence makes the implication true.  The resulting equivalence records that
the old interface is exactly a reformulation of xi hypertranscendence, not an independent RH
input.
-/

namespace RHTower

open Complex Filter Set

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiGlobalUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

/-- The specialized actual xi carrier is the generic rotated entire-function carrier. -/
theorem xiRotatedUpperEndCarrier_eq_rotatedEntireUpperEndMero :
    xiRotatedUpperEndCarrier =
      rotatedEntireUpperEndMero xi xi_analyticOnNhd_univ (-I) := by
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      xiRotatedUpperEndAnalytic =
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (rotatedEntireUpperEndAnalytic xi xi_analyticOnNhd_univ (-I))
  congr 1

/-- **Unconditional completed-xi capstone.**  The Riemann xi function satisfies no nonzero
algebraic differential equation with complex polynomial coefficients. -/
theorem xi_hypertranscendental : Hypertranscendental xi := by
  apply hypertranscendental_of_rotatedEntireUpperEnd_hypertranscendentalOver
    xi_analyticOnNhd_univ (neg_ne_zero.mpr I_ne_zero)
  rw [← xiRotatedUpperEndCarrier_eq_rotatedEntireUpperEndMero]
  exact xiRotatedUpperEndCarrier_hypertranscendentalOver_ratFunc

/-- **Unconditional finite-action mass-clock boundary for Xi.**  The completed Xi function is not
an exact finite sum of complex mass-action exponentials. -/
theorem xi_ne_finiteMassClockSignal
    {I : Type*} [DecidableEq I]
    (s : Finset I) (amplitude action : I → ℂ) :
    xi ≠ HTGeometry.finiteMassClockSignal s amplitude action :=
  HTGeometry.hypertranscendental_ne_finiteMassClockSignal
    xi_hypertranscendental s amplitude action

/-- Global xi hypertranscendence discharges the frequency-collapse interface: the interface's
nonzero differential-relation premise is impossible. -/
theorem xiFrequencyCollapse_of_hypertranscendental
    (hxi : Hypertranscendental xi) : XiFrequencyCollapse := by
  intro m Q hQ hrelation
  exact (hxi ⟨m, Q, hQ, hrelation⟩).elim

/-- The historical frequency-collapse proposition is exactly equivalent to completed-xi
hypertranscendence. -/
theorem xiFrequencyCollapse_iff_hypertranscendental :
    XiFrequencyCollapse ↔ Hypertranscendental xi :=
  ⟨xi_hypertranscendental_of_frequencyCollapse,
    xiFrequencyCollapse_of_hypertranscendental⟩

/-- **Unconditional interface discharge.** -/
theorem xiFrequencyCollapse : XiFrequencyCollapse :=
  xiFrequencyCollapse_of_hypertranscendental xi_hypertranscendental

end

end RHTower
