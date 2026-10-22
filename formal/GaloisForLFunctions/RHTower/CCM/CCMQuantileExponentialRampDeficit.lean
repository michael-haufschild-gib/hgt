import GaloisForLFunctions.RHTower.CCM.CCMQuantileContinuousTestConservation
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitPrimeWork
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinGrowingCumulative

/-!
# Exponential-ramp transport of the actual critical deficit

An exponentially weighted ramp converts critical-Mellin atoms back into
ordinary Mangoldt atoms. Its completed quantile action is exactly the
square-root-normalized logarithmic Chebyshev deficit minus a bounded transient.
This uses the full signed source and both orientations of the terminal cell.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

def ccmNormalizedExponentialRampTest (T : ℝ) : C(ℝ, ℝ) :=
  ⟨fun h => Real.exp ((h-T)/2)*(T-h), by fun_prop⟩

@[simp] theorem ccmNormalizedExponentialRampTest_terminal (T : ℝ) :
    ccmNormalizedExponentialRampTest T T = 0 := by
  simp [ccmNormalizedExponentialRampTest]

theorem ccmNormalizedExponentialRampTest_increment (T s r : ℝ) :
    ccmNormalizedExponentialRampTest T (s+r)-ccmNormalizedExponentialRampTest T s =
      Real.exp ((s-T)/2)*((T-s)*(Real.exp (r/2)-1)-r*Real.exp (r/2)) := by
  have he : Real.exp ((s+r-T)/2) = Real.exp ((s-T)/2)*Real.exp (r/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp ((s+r-T)/2)*(T-(s+r))-Real.exp ((s-T)/2)*(T-s) = _
  rw [he]
  ring

theorem criticalMellinAtomWeight_mul_exponentialRamp (T : ℝ) (n : ℕ) :
    criticalMellinAtomWeight n*ccmNormalizedExponentialRampTest T (Real.log n) =
      Real.exp (-T/2)*(ArithmeticFunction.vonMangoldt n*(T-Real.log n)) := by
  by_cases hn : n = 0
  · simp [hn, criticalMellinAtomWeight]
  · have hw := criticalMellinAtomWeight_mul_exp_log_half (Nat.pos_of_ne_zero hn)
    have he : Real.exp ((Real.log n-T)/2) = Real.exp (-T/2)*Real.exp (Real.log n/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change criticalMellinAtomWeight n*(Real.exp ((Real.log n-T)/2)*(T-Real.log n)) = _
    rw [he]
    calc
      _ = Real.exp (-T/2)*(criticalMellinAtomWeight n*Real.exp (Real.log n/2))*(T-Real.log n) := by ring
      _ = _ := by rw [hw]; ring

private theorem exponential_ramp_background (T : ℝ) :
    (∫ h in (0 : ℝ)..T, Real.exp h*(T-h)) = Real.exp T-T-1 := by
  have hd (h : ℝ) : HasDerivAt (fun u : ℝ => Real.exp u*(T-u+1))
      (Real.exp h*(T-h)) h := by
    convert! (Real.hasDerivAt_exp h).mul (((hasDerivAt_id h).const_sub T).add_const 1) using 1
    simp only [id_eq]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hd h)
    ((by fun_prop : Continuous (fun h : ℝ => Real.exp h*(T-h))).intervalIntegrable 0 T)
  simp only [sub_self, zero_add, mul_one, sub_zero, Real.exp_zero, one_mul] at hi
  linarith only [hi]

theorem integral_ccmNormalizedExponentialRampTest_background (T : ℝ) :
    (∫ h in (0 : ℝ)..T, Real.exp (h/2)*ccmNormalizedExponentialRampTest T h) =
      Real.exp (-T/2)*(Real.exp T-T-1) := by
  have he (h : ℝ) : Real.exp (h/2)*ccmNormalizedExponentialRampTest T h =
      Real.exp (-T/2)*(Real.exp h*(T-h)) := by
    change Real.exp (h/2)*(Real.exp ((h-T)/2)*(T-h)) = _
    rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, exponential_ramp_background]

private theorem sum_prime_tents_range (N : ℕ) (T : ℝ) :
    (∑ n ∈ Finset.range (N+1), ArithmeticFunction.vonMangoldt n*(T-Real.log n)) =
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n*(T-Real.log n) := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    simp [hn0]

/-- The literal completed action is the actual critical deficit with its initial transient removed. -/
theorem ccmActualTimeExponentialRampAction_eq_normalizedDeficit (H : NNReal) :
    ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
      (ccmNormalizedExponentialRampTest (H : ℝ)) =
        Real.exp (-(H : ℝ)/2)*(ccmLogChebyshevDeficitPrimitive (H : ℝ)-(H : ℝ)) := by
  rw [ccmActualHeadQuantileTestAction_eq_source_balance,
    ccmNormalizedExponentialRampTest_terminal, mul_zero, sub_zero,
    integral_ccmNormalizedExponentialRampTest_background]
  simp_rw [criticalMellinAtomWeight_mul_exponentialRamp]
  rw [← Finset.mul_sum, sum_prime_tents_range,
    ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents H.coe_nonneg]
  ring

def ccmExponentialRampDisplacementWeight (r : ℝ) : ℝ := Real.exp (r/2)-1

def ccmExponentialRampDerivativeWeight (r : ℝ) : ℝ := -r*Real.exp (r/2)

def ccmActualHeadExponentialRampPositionField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
    Real.exp ((Real.log n-T)/2)*(T-Real.log n)

def ccmActualHeadExponentialRampMassField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
    Real.exp ((Real.log n-T)/2)) + ccmActualHeadQuantileTerminalDisplacementDensity T N r

/-- Two literal transport fields contain the full signed critical remainder current. -/
theorem ccmActualHeadExponentialRampCurrent_eq_two_fields (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r =
      ccmExponentialRampDisplacementWeight r*ccmActualHeadExponentialRampPositionField T N r +
        ccmExponentialRampDerivativeWeight r*ccmActualHeadExponentialRampMassField T N r := by
  have hc (n : ℕ) : ccmOutgoingQuantileDisplacementCellDensity n r *
      (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n)) =
      ccmExponentialRampDisplacementWeight r*(ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.exp ((Real.log n-T)/2)*(T-Real.log n)) +
      ccmExponentialRampDerivativeWeight r*(ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.exp ((Real.log n-T)/2)) := by
    rw [ccmNormalizedExponentialRampTest_increment]
    unfold ccmExponentialRampDisplacementWeight ccmExponentialRampDerivativeWeight
    ring
  have ht : ccmActualHeadQuantileTerminalDisplacementDensity T N r *
      (ccmNormalizedExponentialRampTest T (T+r)-ccmNormalizedExponentialRampTest T T) =
      ccmExponentialRampDerivativeWeight r*ccmActualHeadQuantileTerminalDisplacementDensity T N r := by
    rw [ccmNormalizedExponentialRampTest_increment]
    simp only [sub_self, zero_div, Real.exp_zero, zero_mul, zero_sub, one_mul]
    unfold ccmExponentialRampDerivativeWeight
    ring
  unfold ccmActualHeadQuantileTestCurrent ccmActualHeadExponentialRampPositionField
    ccmActualHeadExponentialRampMassField
  simp_rw [hc]
  rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem normalized_chebyshevDeficit_eq_exponentialRampTransport (H : NNReal) :
    Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ) =
      (H : ℝ)*Real.exp (-(H : ℝ)/2) +
        ∫ r : ℝ,
          ccmExponentialRampDisplacementWeight r*ccmActualHeadExponentialRampPositionField
            (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1) r +
          ccmExponentialRampDerivativeWeight r*ccmActualHeadExponentialRampMassField
            (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1) r := by
  have h := ccmActualTimeExponentialRampAction_eq_normalizedDeficit H
  unfold ccmActualHeadQuantileTestAction at h
  simp_rw [ccmActualHeadExponentialRampCurrent_eq_two_fields] at h
  linarith only [h]

theorem ccmExponentialRampTransient_bound (H : NNReal) :
    |(H : ℝ)*Real.exp (-(H : ℝ)/2)| ≤ 2 := by
  rw [abs_of_nonneg (mul_nonneg H.coe_nonneg (Real.exp_pos _).le)]
  have h := Real.add_one_le_exp ((H : ℝ)/2)
  have hlin : (H : ℝ) ≤ 2*Real.exp ((H : ℝ)/2) := by linarith only [h]
  have hb := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(H : ℝ)/2)).le
  have he : Real.exp ((H : ℝ)/2)*Real.exp (-(H : ℝ)/2) = 1 := by
    rw [← Real.exp_add, show (H : ℝ)/2+(-(H : ℝ)/2) = 0 by ring, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using hb

end RHTower
