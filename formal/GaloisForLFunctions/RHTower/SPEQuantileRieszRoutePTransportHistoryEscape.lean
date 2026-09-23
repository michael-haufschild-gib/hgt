import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePUnitRieszRenewalBridge
import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePWeightedCreditEscape

/-!
# Exact P/SP-E transport credit and cofinal geometric mismatch

The signed weighted-Chebyshev credit of the literal P prime-power history is
minus one half of the separately constructed SP-E completed quantile Riesz
transport at the same physical endpoint. Even after adding twice that complete
transport to the mass-normalized P history, a positive prime-two centroid
excess forces the result to negative infinity. Thus the two source quantities
cannot be identified without an unbounded geometric correction; this is not
an ordered-history graph intertwiner or an RH proof.
-/

open Filter

namespace RHTower

theorem routePWeightedChebyshevNullCredit_eq_neg_half_speTransport (K : ℕ) :
    routePWeightedChebyshevNullCredit K =
      -speCompletedQuantileRieszTransport (K + 2) / 2 := by
  have hM : (0 : ℝ) < ((K + 2 : ℕ) : ℝ) := by positivity
  have hsource := speCompletedQuantileRieszTransport_div_eq_resolvent_source
    (M := K + 2) (show 2 ≤ K + 2 by omega)
  rw [routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source,
    ← hsource]
  field_simp [hM.ne']

theorem routeP_normalized_history_add_two_speTransport_tendsto_atBot :
    Tendsto
      (fun K : ℕ =>
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K +
          2 * speCompletedQuantileRieszTransport (K + 2))
      atTop atBot := by
  convert routeP_history_sub_credit_tendsto_atBot using 1
  funext K
  rw [routePWeightedChebyshevNullCredit_eq_neg_half_speTransport]
  ring

end RHTower
