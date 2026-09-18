import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCompletedCenteredBoundary

/-!
# Endpoint-quartic law for the literal completed parabolic source

The finite strict-cross current, its signed covariance, squared displacement debt, and terminal
interaction are not independent completed quantities.  On the literal completed carrier, the
quantile side concatenates to one physical polar interval.  Its entire parabolic form is therefore
the fourth power of that interval's physical mass.  The remaining term is exactly the form of the
actual matched prime--polar aggregate.

This is an identity of the original completed source, not a replacement reporter or an estimate.
It identifies the analytic frontier as comparison of the actual matched aggregate form with the
physical polar endpoint quartic.  No sign, asymptotic, convergence claim, or RH premise enters.
-/

noncomputable section

namespace RHTower

/-- **Literal completed endpoint law.** The complete matched-minus-quantile source current is
the actual matched aggregate form minus the fourth-power form of the one physical polar endpoint
interval.  Hence covariance, displacement debt, and terminal interaction can be controlled only
through their exact joint source cancellation. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolic_pairing_sourceBoundary_eq_matchedForm_sub_endpointQuartic
    (K : ℕ) (T : ℝ) :
    ccmParabolicPairing (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T)
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T) =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        (ccmActualHeadPolarMassCoordinate T -
          ccmActualHeadQuantilePolarCoordinate 2) ^ 4 / 12 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadCompletedQuantileParabolicAggregate_eq_moment,
    ccmParabolicForm_moment]

/-- The physical polar mass coordinate at the canonical logarithmic clock is exactly twice the
square root of its integer endpoint. -/
theorem ccmActualHeadPolarMassCoordinate_log_nat (N : ℕ) (hN : 0 < N) :
    ccmActualHeadPolarMassCoordinate (Real.log (N : ℝ)) =
      2 * Real.sqrt (N : ℝ) := by
  unfold ccmActualHeadPolarMassCoordinate
  congr 1
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsq : Real.exp (Real.log (N : ℝ) / 2) ^ 2 = (N : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    have hsum : Real.log (N : ℝ) / 2 + Real.log (N : ℝ) / 2 =
        Real.log (N : ℝ) := by ring
    rw [hsum, Real.exp_log hNR]
  nlinarith [Real.exp_pos (Real.log (N : ℝ) / 2),
    Real.sqrt_pos.2 hNR, Real.sq_sqrt hNR.le]

/-- **Canonical-clock endpoint law.** At the literal clock `log (K + 3)`, the completed source
current is the actual matched aggregate form minus the deterministic physical polar quartic.
All remaining arithmetic freedom is therefore inside the matched prime--polar aggregate itself;
no covariance, debt, or terminal term has been estimated away. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolic_pairing_sourceBoundary_log_eq_matchedForm_sub_canonicalEndpointQuartic
    (K : ℕ) :
    ccmParabolicPairing
        (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K (Real.log (K + 3)))
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3))) =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        (2 * Real.sqrt ((K + 3 : ℕ) : ℝ) - 2) ^ 4 / 12 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolic_pairing_sourceBoundary_eq_matchedForm_sub_endpointQuartic]
  have hcast : (K : ℝ) + 3 = ((K + 3 : ℕ) : ℝ) := by norm_num
  rw [hcast,
    ccmActualHeadPolarMassCoordinate_log_nat (K + 3) (by omega),
    ccmActualHeadQuantilePolarCoordinate_two]

end RHTower
