import GaloisForLFunctions.RHTower.CCMCoherentSignedMomentCharge

/-!
# Continuous-test arithmetic conservation

Every continuous test gives a literal signed transport current. Its integral
equals the continuous source minus the prime source and the oriented terminal
mass. Constant shifts of the test leave the current unchanged. This is the
test-action symmetry corresponding to exact completed-source mass conservation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

private def testIncrement (F : C(ℝ, ℝ)) (s : ℝ) : C(ℝ, ℝ) :=
  ⟨fun r => F (s+r)-F s, by fun_prop⟩

def ccmActualHeadQuantileTestCurrent (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) (r : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
    (F (Real.log n+r)-F (Real.log n))) +
  ccmActualHeadQuantileTerminalDisplacementDensity T N r*(F (T+r)-F T)

theorem integrable_ccmActualHeadQuantileTestCurrent (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    Integrable (ccmActualHeadQuantileTestCurrent T N F) := by
  exact (integrable_finsetSum (Finset.range N) (fun n _ =>
    integrable_ccmOutgoingQuantileCellDensity_continuousTest n (testIncrement F (Real.log n)))).add
      (integrable_ccmActualHeadQuantileTerminalDensity_continuousTest T N (testIncrement F T))

def ccmActualHeadQuantileTestAction (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) : ℝ :=
  ∫ r : ℝ, ccmActualHeadQuantileTestCurrent T N F r

private theorem cell_test_balance (n : ℕ) (F : C(ℝ, ℝ)) :
    (∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
      (F (Real.log n+r)-F (Real.log n))) =
      (∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n+1),
        Real.exp (h/2)*F h) - criticalMellinAtomWeight n*F (Real.log n) := by
  rw [integral_ccmOutgoingQuantileCellDensity_mul]
  have he (h : ℝ) : Real.log n+(h-Real.log n) = h := by ring
  simp_rw [he]
  have hf : Continuous (fun h : ℝ => Real.exp (h/2)*F h) := by fun_prop
  have hc : Continuous (fun h : ℝ => Real.exp (h/2)*F (Real.log n)) := by fun_prop
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, integral_exp_half_quantileCell_eq_atomWeight]

private theorem terminal_test_balance (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    (∫ r : ℝ, ccmActualHeadQuantileTerminalDisplacementDensity T N r*(F (T+r)-F T)) =
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T, Real.exp (h/2)*F h) -
        (2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N))*F T := by
  rw [integral_ccmActualHeadQuantileTerminalDensity_mul]
  have he (h : ℝ) : T+(h-T) = h := by ring
  simp_rw [he]
  have hf : Continuous (fun h : ℝ => Real.exp (h/2)*F h) := by fun_prop
  have hc : Continuous (fun h : ℝ => Real.exp (h/2)*F T) := by fun_prop
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, integral_exp_half_quantileBoundary_to_eq_massMismatch]

/-- Exact source conservation for every continuous test, including terminal overshoot. -/
theorem ccmActualHeadQuantileTestAction_eq_source_balance
    (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    ccmActualHeadQuantileTestAction T N F =
      (∫ h in (0 : ℝ)..T, Real.exp (h/2)*F h) -
        (∑ n ∈ Finset.range N, criticalMellinAtomWeight n*F (Real.log n)) -
          (2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N))*F T := by
  have hc (n : ℕ) : Integrable (fun r => ccmOutgoingQuantileDisplacementCellDensity n r *
      (F (Real.log n+r)-F (Real.log n))) :=
    integrable_ccmOutgoingQuantileCellDensity_continuousTest n (testIncrement F (Real.log n))
  have ht : Integrable (fun r => ccmActualHeadQuantileTerminalDisplacementDensity T N r*(F (T+r)-F T)) :=
    integrable_ccmActualHeadQuantileTerminalDensity_continuousTest T N (testIncrement F T)
  have hF : Continuous (fun h : ℝ => Real.exp (h/2)*F h) := by fun_prop
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := ccmOutgoingPrimeQuantileBoundary) (n := N)
    (fun k _ => hF.intervalIntegrable (μ := volume) (ccmOutgoingPrimeQuantileBoundary k)
      (ccmOutgoingPrimeQuantileBoundary (k+1)))
  rw [ccmOutgoingPrimeQuantileBoundary_zero] at hs
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) 0 (ccmOutgoingPrimeQuantileBoundary N))
    (hF.intervalIntegrable (ccmOutgoingPrimeQuantileBoundary N) T)
  unfold ccmActualHeadQuantileTestAction ccmActualHeadQuantileTestCurrent
  rw [integral_add (integrable_finsetSum (Finset.range N) (fun n _ => hc n)) ht,
    integral_finsetSum _ (fun n _ => hc n)]
  simp_rw [cell_test_balance]
  rw [Finset.sum_sub_distrib, hs, terminal_test_balance, ← ha]
  ring

/-- Adding a constant to the test is an exact pointwise current symmetry. -/
theorem ccmActualHeadQuantileTestCurrent_add_constant
    (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) (c r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (F+ContinuousMap.const ℝ c) r =
      ccmActualHeadQuantileTestCurrent T N F r := by
  simp [ccmActualHeadQuantileTestCurrent]

theorem ccmActualHeadQuantileTestAction_add_constant
    (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) (c : ℝ) :
    ccmActualHeadQuantileTestAction T N (F+ContinuousMap.const ℝ c) =
      ccmActualHeadQuantileTestAction T N F := by
  unfold ccmActualHeadQuantileTestAction
  simp_rw [ccmActualHeadQuantileTestCurrent_add_constant]

theorem ccmActualHeadQuantileTestAction_const (T : ℝ) (N : ℕ) (c : ℝ) :
    ccmActualHeadQuantileTestAction T N (ContinuousMap.const ℝ c) = 0 := by
  simp [ccmActualHeadQuantileTestAction, ccmActualHeadQuantileTestCurrent]

/-- The conserved mass is the coefficient of the continuous constant-shift action. -/
theorem ccmActualHeadQuantileCompletedSource_mass_balance (T : ℝ) (N : ℕ) :
    (∫ h in (0 : ℝ)..T, Real.exp (h/2)) =
      ccmOutgoingPrimeCumulative N + (2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N)) := by
  have h := ccmActualHeadQuantileTestAction_eq_source_balance T N (ContinuousMap.const ℝ 1)
  rw [ccmActualHeadQuantileTestAction_const] at h
  simp only [ContinuousMap.const_apply, mul_one] at h
  change 0 = (∫ h in (0 : ℝ)..T, Real.exp (h/2))-ccmOutgoingPrimeCumulative N-
    (2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N)) at h
  linarith only [h]

end RHTower
