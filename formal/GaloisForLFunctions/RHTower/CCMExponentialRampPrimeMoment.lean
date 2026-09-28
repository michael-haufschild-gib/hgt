import GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation

/-!
# Nonlinear prime forcing of the transport age moment

After multiplication by the growing half-density, cell displacement moments
telescope to the square of the critical prime cumulative minus the ordinary
Mangoldt cumulative. This identifies the exact arithmetic forcing of the
fixed-head age-moment equation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

theorem ccmExponentialRampCellDisplacementMoment_mul_exp (n : ℕ) :
    ccmExponentialRampCellDisplacementMoment n*Real.exp (Real.log n/2) =
      Real.exp (ccmOutgoingPrimeQuantileBoundary (n+1))-
        Real.exp (ccmOutgoingPrimeQuantileBoundary n)-ArithmeticFunction.vonMangoldt n := by
  have hw : criticalMellinAtomWeight n*Real.exp (Real.log n/2) = ArithmeticFunction.vonMangoldt n := by
    by_cases hn : n = 0
    · simp [hn, criticalMellinAtomWeight]
    · exact criticalMellinAtomWeight_mul_exp_log_half (Nat.pos_of_ne_zero hn)
  have he (h : ℝ) : Real.exp (h/2)*ccmExponentialRampDisplacementWeight (h-Real.log n) =
      Real.exp (-Real.log n/2)*Real.exp h-Real.exp (h/2) := by
    unfold ccmExponentialRampDisplacementWeight
    rw [mul_sub, mul_one, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hi₁ : IntervalIntegrable (fun h : ℝ => Real.exp (-Real.log n/2)*Real.exp h) volume
      (ccmOutgoingPrimeQuantileBoundary n) (ccmOutgoingPrimeQuantileBoundary (n+1)) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)) volume
      (ccmOutgoingPrimeQuantileBoundary n) (ccmOutgoingPrimeQuantileBoundary (n+1)) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hx : Real.exp (-Real.log n/2)*Real.exp (Real.log n/2) = 1 := by
    rw [← Real.exp_add, show -Real.log n/2+Real.log n/2 = 0 by ring, Real.exp_zero]
  unfold ccmExponentialRampCellDisplacementMoment
  rw [integral_ccmOutgoingQuantileCellDensity_mul]
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul,
    integral_exp, integral_exp_half_quantileCell_eq_atomWeight]
  linear_combination (Real.exp (ccmOutgoingPrimeQuantileBoundary (n+1))-
    Real.exp (ccmOutgoingPrimeQuantileBoundary n))*hx-hw

def ccmExponentialRampPrimeMomentCumulative (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmExponentialRampCellDisplacementMoment n*Real.exp (Real.log n/2)

theorem ccmExponentialRampPrimeMomentCumulative_eq_boundary (N : ℕ) :
    ccmExponentialRampPrimeMomentCumulative N = Real.exp (ccmOutgoingPrimeQuantileBoundary N)-1-
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n := by
  unfold ccmExponentialRampPrimeMomentCumulative
  simp_rw [ccmExponentialRampCellDisplacementMoment_mul_exp]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub]
  simp only [ccmOutgoingPrimeQuantileBoundary_zero, Real.exp_zero]

/-- An exact nonlinear discrepancy involving only the two literal prime cumulatives. -/
theorem ccmExponentialRampPrimeMomentCumulative_eq_primeDiscrepancy (N : ℕ) :
    ccmExponentialRampPrimeMomentCumulative N =
      ccmOutgoingPrimeCumulative N+(ccmOutgoingPrimeCumulative N)^2/4-
        ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n := by
  rw [ccmExponentialRampPrimeMomentCumulative_eq_boundary]
  have he : Real.exp (ccmOutgoingPrimeQuantileBoundary N) =
      (1+ccmOutgoingPrimeCumulative N/2)^2 := by
    rw [← exp_half_ccmOutgoingPrimeQuantileBoundary, sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem ccmExponentialRampAgeForce_eq_moment_sub_primeForcing (T : ℝ) (N : ℕ) :
    ccmExponentialRampAgeForce T N = ccmExponentialRampAgeMoment T N-
      2*Real.exp (-T/2)*ccmExponentialRampPrimeMomentCumulative N := by
  have he (n : ℕ) : Real.exp ((Real.log n-T)/2) = Real.exp (-T/2)*Real.exp (Real.log n/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ccmExponentialRampAgeForce_eq_cellMoments]
  unfold ccmExponentialRampAgeMoment ccmExponentialRampPrimeMomentCumulative
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [he]
  ring

/-- The age moment obeys a damped equation driven by the literal nonlinear prime discrepancy. -/
theorem ccmExponentialRampAgeMoment_damped_primeEquation (T : ℝ) (N : ℕ) :
    deriv (fun t => ccmExponentialRampAgeMoment t N) T+
      (1/2 : ℝ)*ccmExponentialRampAgeMoment T N =
        Real.exp (-T/2)*(ccmOutgoingPrimeCumulative N+(ccmOutgoingPrimeCumulative N)^2/4-
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n) := by
  rw [(hasDerivAt_ccmExponentialRampAgeMoment T N).deriv,
    ccmExponentialRampAgeForce_eq_moment_sub_primeForcing,
    ccmExponentialRampPrimeMomentCumulative_eq_primeDiscrepancy]
  ring

theorem ccmExponentialRampAction_nonlinear_primeBalance (T : ℝ) (N : ℕ) :
    ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)+
      ccmExponentialRampBulkDissipation T N+2*Real.exp (-T/2)*
        (ccmOutgoingPrimeCumulative N+(ccmOutgoingPrimeCumulative N)^2/4-
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n) =
            ccmExponentialRampAgeMoment T N+ccmExponentialRampTerminalEntropy T N := by
  have h := ccmExponentialRampAction_source_dissipation T N
  rw [ccmExponentialRampAgeForce_eq_moment_sub_primeForcing,
    ccmExponentialRampPrimeMomentCumulative_eq_primeDiscrepancy] at h
  linarith only [h]

end RHTower
