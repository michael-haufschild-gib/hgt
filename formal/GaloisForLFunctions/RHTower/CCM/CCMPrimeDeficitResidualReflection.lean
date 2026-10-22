import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitResidualPairing

/-!
# Reflection of the complete cutoff defect at every scale

The actual defect is a reflection pairing of the residual divisor count
with an exponential-minus-logarithmic residual force. Every cutoff and
every nonnegative terminal time is admitted; no square-root-window
restriction or unproved cancellation estimate is used.
-/

noncomputable section
open MeasureTheory

namespace RHTower

theorem logarithmicWeightedDilation_pair_exponentialRamp_eq_reflection
    (w v : ℕ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation v logarithmicExponentialRamp) T =
      ∫ s in (0 : ℝ)..T,
        logarithmicFiniteEntryProfile w ⌊Real.exp T⌋₊ Real.exp s *
          logarithmicFiniteEntryProfile v ⌊Real.exp T⌋₊ (fun _ => 1) (T - s) := by
  rw [logarithmicWeightedDilation_pair_eq_square _ _ _
    (fun _ ht => logarithmicExponentialRamp_of_nonpos ht.le)]
  exact (integral_logarithmicFiniteExponentialEntry_pair w v ⌊Real.exp T⌋₊ T).symm

theorem logarithmicWeightedDilation_pair_linearRamp_eq_reflection
    (w v : ℕ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation v logarithmicLinearRamp) T =
      ∫ s in (0 : ℝ)..T,
        logarithmicFiniteEntryProfile w ⌊Real.exp T⌋₊ (fun _ => 1) s *
          logarithmicFiniteEntryProfile v ⌊Real.exp T⌋₊ (fun _ => 1) (T - s) := by
  rw [logarithmicWeightedDilation_pair_eq_square _ _ _
    (fun _ ht => logarithmicLinearRamp_of_nonpos ht.le)]
  exact (integral_logarithmicFiniteUnitEntry_pair w v ⌊Real.exp T⌋₊ T).symm

def ccmPrimeDeficitResidualCountProfile (m U : ℕ) (t : ℝ) : ℝ :=
  logarithmicFiniteEntryProfile (ccmPrimeDeficitResidualCoeff m) U (fun _ => 1) t

def ccmPrimeDeficitResidualForce (m U : ℕ) (t : ℝ) : ℝ :=
  logarithmicFiniteEntryProfile (ccmPrimeDeficitResidualCoeff m) U Real.exp t -
    logarithmicFiniteEntryProfile (ccmPrimeDeficitResidualLogCoeff m) U (fun _ => 1) t

theorem intervalIntegrable_ccmPrimeDeficitResidualReflection (m U : ℕ) (T a b : ℝ) :
    IntervalIntegrable (fun s => ccmPrimeDeficitResidualForce m U s *
      ccmPrimeDeficitResidualCountProfile m U (T - s)) volume a b := by
  have he := intervalIntegrable_logarithmicFiniteExponentialEntry_pair
    (ccmPrimeDeficitResidualCoeff m) (ccmPrimeDeficitResidualCoeff m) U T a b
  have hl := intervalIntegrable_logarithmicFiniteUnitEntry_pair
    (ccmPrimeDeficitResidualLogCoeff m) (ccmPrimeDeficitResidualCoeff m) U T a b
  apply (he.sub hl).congr
  intro s _
  exact (sub_mul _ _ _).symm

/-- A global signed reflection identity for the actual arithmetic defect.
The retained action is arbitrary: no relation between `m` and `exp(T/2)`
is required. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_residual_reflection
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      ∫ s in (0 : ℝ)..T, ccmPrimeDeficitResidualForce m ⌊Real.exp T⌋₊ s *
        ccmPrimeDeficitResidualCountProfile m ⌊Real.exp T⌋₊ (T - s) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_residual_pair m hT,
    logarithmicWeightedDilation_pair_exponentialRamp_eq_reflection,
    logarithmicWeightedDilation_pair_linearRamp_eq_reflection,
    ← intervalIntegral.integral_sub
      (intervalIntegrable_logarithmicFiniteExponentialEntry_pair _ _ _ _ _ _)
      (intervalIntegrable_logarithmicFiniteUnitEntry_pair _ _ _ _ _ _)]
  apply intervalIntegral.integral_congr
  intro s _
  exact (sub_mul _ _ _).symm

end RHTower
