import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFiniteGraphHistory
import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryTransport

/-!
# SP-E/P vertical terminal-connection cocycle

The finite P graph carrier must keep the terminal connection as an independent
extension coordinate: it is not the source radical.  This file identifies its
source-defined value exactly.  The terminal change is the complete signed
prime-power history with the physical moving-wall transport subtracted;
equivalently it is the strict-cross source change with that transport
subtracted.

Thus the required vertical coordinate is not a target-chosen correction.  It
is a literal cocycle of the retained source data.  This identity supplies no
cofinal graph action, growth estimate, or divisor landing; those remain the
substantive Route-P/SP-E problem.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The source-defined vertical coordinate which remains after subtracting the
physical moving-wall transport from the complete strict-cross source change. -/
def speQuantileRieszRoutePVerticalConnectionDefect (K : ℕ) : ℝ :=
  ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 0)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary 0) -
    ∑ n ∈ Finset.range K, speQuantileRieszPhysicalWallDynamicSourceTransport n

/-- The terminal connection change is the literal prime-power history less
the accumulated moving-wall transport.  All zero-atom cancellations remain in
the prime-power history theorem used here; no source term is discarded. -/
theorem speQuantileRieszTerminalConnection_sub_zero_eq_primePowerHistory_sub_dynamicTransport
    (K : ℕ) :
    speQuantileRieszCanonicalTerminalConnection K -
        speQuantileRieszCanonicalTerminalConnection 0 =
      (∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
        speQuantileRieszPrimePowerHistoryCurvature n) -
      ∑ n ∈ Finset.range K, speQuantileRieszPhysicalWallDynamicSourceTransport n := by
  have h :=
    sum_speQuantileRieszDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistory K
  rw [Finset.sum_add_distrib, Finset.sum_range_sub] at h
  linarith

/-- The exact source vertical defect is precisely the terminal connection
change.  This makes the terminal coordinate available to a future unbounded
two-Julia graph closure without identifying it with the source radical. -/
theorem speQuantileRieszTerminalConnection_sub_zero_eq_routePVerticalConnectionDefect
    (K : ℕ) :
    speQuantileRieszCanonicalTerminalConnection K -
        speQuantileRieszCanonicalTerminalConnection 0 =
      speQuantileRieszRoutePVerticalConnectionDefect K := by
  rw [speQuantileRieszRoutePVerticalConnectionDefect,
    ccmActualHeadMatchedQuantileParabolicStrictCross_sub_zero_eq_primePowerHistory]
  exact speQuantileRieszTerminalConnection_sub_zero_eq_primePowerHistory_sub_dynamicTransport K

end

end RHTower
