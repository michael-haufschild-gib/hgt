import GaloisForLFunctions.RHTower.CCMCoherentExteriorMomentGammaLimit
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam

/-!
# Arithmetic charge of the signed midpoint moment

The displacement-weighted first frequency moment is exactly the curvature of
the completed prime--polar characteristic symbol. Every quantile cell and the
oriented terminal cell is retained. No sign or cancellation premise is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

/-- Testing a displaced prime cell is exactly testing its original mass interval. -/
theorem integral_ccmOutgoingQuantileCellDensity_mul (n : ℕ) (F : ℝ → ℝ) :
    (∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r * F r) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n+1),
        Real.exp (h/2)*F (h-Real.log n) := by
  let G := fun r : ℝ => Real.exp ((r+Real.log n)/2)*F r
  have hs := intervalIntegral.integral_comp_sub_right
    (a := ccmOutgoingPrimeQuantileBoundary n)
    (b := ccmOutgoingPrimeQuantileBoundary (n+1)) G (Real.log n)
  have he : (∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n+1), Real.exp (h/2)*F (h-Real.log n)) =
      ∫ r in (ccmOutgoingPrimeQuantileBoundary n-Real.log n)..
        (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n), G r := by
    simpa only [G, sub_add_cancel] using hs
  rw [he, intervalIntegral.integral_of_le
    (sub_le_sub_right (ccmOutgoingPrimeQuantileBoundary_mono_step n) (Real.log n)),
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
      (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) <;>
    simp [ccmOutgoingQuantileDisplacementCellDensity, G, hr]

/-- The terminal test formula is valid for both endpoint orientations. -/
theorem integral_ccmActualHeadQuantileTerminalDensity_mul (T : ℝ) (N : ℕ) (F : ℝ → ℝ) :
    (∫ r : ℝ, ccmActualHeadQuantileTerminalDisplacementDensity T N r * F r) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary N..T, Real.exp (h/2)*F (h-T) := by
  let G := fun r : ℝ => Real.exp ((r+T)/2)*F r
  have hs := intervalIntegral.integral_comp_sub_right
    (a := ccmOutgoingPrimeQuantileBoundary N) (b := T) G T
  have he : (∫ h in ccmOutgoingPrimeQuantileBoundary N..T, Real.exp (h/2)*F (h-T)) =
      ∫ r in (ccmOutgoingPrimeQuantileBoundary N-T)..0, G r := by
    simpa only [G, sub_add_cancel, sub_self] using hs
  rw [he]
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · rw [intervalIntegral.integral_of_le (sub_nonpos.mpr hb),
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary N-T) 0 <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, G, hb, hr]
  · rw [intervalIntegral.integral_symm,
      intervalIntegral.integral_of_le (sub_nonneg.mpr (le_of_not_ge hb)),
      ← integral_indicator measurableSet_Ioc, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N-T) <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, G, hb, hr]

private theorem integrable_indicator_continuous (lo hi : ℝ) (F : ℝ → ℝ)
    (hF : Continuous F) : Integrable ((Ioc lo hi).indicator F) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact hF.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem integrable_cell_test (n : ℕ) (F : ℝ → ℝ) (hF : Continuous F) :
    Integrable (fun r => ccmOutgoingQuantileDisplacementCellDensity n r * F r) := by
  have h := integrable_indicator_continuous
    (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n)
    (fun r => Real.exp ((r+Real.log n)/2)*F r) (by fun_prop)
  refine h.congr (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
      (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) <;>
    simp [ccmOutgoingQuantileDisplacementCellDensity, hr]

private theorem integrable_terminal_test (T : ℝ) (N : ℕ) (F : ℝ → ℝ) (hF : Continuous F) :
    Integrable (fun r => ccmActualHeadQuantileTerminalDisplacementDensity T N r * F r) := by
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · have h := integrable_indicator_continuous (ccmOutgoingPrimeQuantileBoundary N-T) 0
      (fun r => Real.exp ((r+T)/2)*F r) (by fun_prop)
    refine h.congr (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary N-T) 0 <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr]
  · have h := (integrable_indicator_continuous 0 (ccmOutgoingPrimeQuantileBoundary N-T)
      (fun r => Real.exp ((r+T)/2)*F r) (by fun_prop)).neg
    refine h.congr (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N-T) <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr]

/-- Every continuous displacement test is integrable against an actual prime cell. -/
theorem integrable_ccmOutgoingQuantileCellDensity_continuousTest (n : ℕ) (F : C(ℝ, ℝ)) :
    Integrable (fun r => ccmOutgoingQuantileDisplacementCellDensity n r * F r) :=
  integrable_cell_test n F F.continuous

/-- Continuous tests remain integrable for either orientation of the terminal cell. -/
theorem integrable_ccmActualHeadQuantileTerminalDensity_continuousTest
    (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    Integrable (fun r => ccmActualHeadQuantileTerminalDisplacementDensity T N r * F r) :=
  integrable_terminal_test T N F F.continuous

private theorem integrable_cell_charge (n : ℕ) :
    Integrable (fun r : ℝ => r*(ccmOutgoingQuantileDisplacementCellDensity n r *
      (2*Real.pi*(Real.log n+r/2)))) := by
  have h := integrable_cell_test n (fun r => r*(2*Real.pi*(Real.log n+r/2))) (by fun_prop)
  exact h.congr (Eventually.of_forall fun r => by ring)

private theorem integrable_terminal_charge (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => r*(ccmActualHeadQuantileTerminalDisplacementDensity T N r *
      (2*Real.pi*(T+r/2)))) := by
  have h := integrable_terminal_test T N (fun r => r*(2*Real.pi*(T+r/2))) (by fun_prop)
  exact h.congr (Eventually.of_forall fun r => by ring)

theorem integrable_ccmActualHeadSignedMoment_displacement (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => r*ccmActualHeadMidpointSignedMoment T N r) := by
  have h := (integrable_finsetSum (Finset.range N) (fun n _ => integrable_cell_charge n)).add
    (integrable_terminal_charge T N)
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, ccmActualHeadMidpointSignedMoment, mul_add, Finset.mul_sum]

/-- The signed displacement moment of the literal completed arithmetic packet. -/
def ccmActualHeadSignedMomentCharge (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, r*ccmActualHeadMidpointSignedMoment T N r

theorem integral_ccmOutgoingQuantileCell_signedMoment (n : ℕ) :
    (∫ r : ℝ, r*(ccmOutgoingQuantileDisplacementCellDensity n r *
      (2*Real.pi*(Real.log n+r/2)))) =
    -Real.pi*(criticalMellinAtomWeight n*(Real.log n)^2 -
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n+1),
        Real.exp (h/2)*h^2) := by
  rw [ccmActualHeadOutgoingQuantileMomentError_eq_displacementMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  ring

theorem integral_ccmActualHeadQuantileTerminal_signedMoment (T : ℝ) (N : ℕ) :
    (∫ r : ℝ, r*(ccmActualHeadQuantileTerminalDisplacementDensity T N r *
      (2*Real.pi*(T+r/2)))) =
    -Real.pi*((2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N))*T^2 -
      ∫ h in ccmOutgoingPrimeQuantileBoundary N..T, Real.exp (h/2)*h^2) := by
  have ht := integral_ccmActualHeadQuantileTerminalDensity_mul T N
    (fun r => r*(2*Real.pi*(T+r/2)))
  have he : (fun r : ℝ => r*(ccmActualHeadQuantileTerminalDisplacementDensity T N r *
      (2*Real.pi*(T+r/2)))) =
      fun r => ccmActualHeadQuantileTerminalDisplacementDensity T N r *
        (r*(2*Real.pi*(T+r/2))) := by funext r; ring
  rw [he, ht]
  have h0 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)) volume
      (ccmOutgoingPrimeQuantileBoundary N) T := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*h^2) volume
      (ccmOutgoingPrimeQuantileBoundary N) T := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [← integral_exp_half_quantileBoundary_to_eq_massMismatch T N,
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub (h0.mul_const _) h2,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro h _
  ring

/-- All quantile-cell moments telescope, including the oriented terminal interval. -/
theorem ccmActualHeadSignedMomentCharge_eq_completedMoment (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentCharge T N = -Real.pi *
      ((∑ n ∈ Finset.range N, criticalMellinAtomWeight n*(Real.log n)^2) +
        (2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N))*T^2 -
        ∫ h in (0 : ℝ)..T, Real.exp (h/2)*h^2) := by
  have hF : Continuous (fun h : ℝ => Real.exp (h/2)*h^2) := by fun_prop
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := ccmOutgoingPrimeQuantileBoundary) (n := N)
    (fun k _ => hF.intervalIntegrable (μ := volume) (ccmOutgoingPrimeQuantileBoundary k)
      (ccmOutgoingPrimeQuantileBoundary (k+1)))
  rw [ccmOutgoingPrimeQuantileBoundary_zero] at hs
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) 0 (ccmOutgoingPrimeQuantileBoundary N))
    (hF.intervalIntegrable (ccmOutgoingPrimeQuantileBoundary N) T)
  have he (r : ℝ) : r*ccmActualHeadMidpointSignedMoment T N r =
      (∑ n ∈ Finset.range N, r*(ccmOutgoingQuantileDisplacementCellDensity n r *
        (2*Real.pi*(Real.log n+r/2)))) +
      r*(ccmActualHeadQuantileTerminalDisplacementDensity T N r*(2*Real.pi*(T+r/2))) := by
    rw [ccmActualHeadMidpointSignedMoment, mul_add, Finset.mul_sum]
  unfold ccmActualHeadSignedMomentCharge
  simp_rw [he]
  rw [integral_add (integrable_finsetSum (Finset.range N) (fun n _ => integrable_cell_charge n))
      (integrable_terminal_charge T N),
    integral_finsetSum _ (fun n _ => integrable_cell_charge n)]
  simp_rw [integral_ccmOutgoingQuantileCell_signedMoment]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hs,
    integral_ccmActualHeadQuantileTerminal_signedMoment, ← ha]
  ring

/-- The surviving arithmetic charge is exactly completed characteristic curvature. -/
theorem ccmActualHeadCompletedCosineCurvature_eq_signedMomentCharge (T : ℝ) (N : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T)) 0 =
      -4*Real.pi*ccmActualHeadSignedMomentCharge T N := by
  rw [ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_secondDeriv_zero,
    ccmActualHeadSignedMomentCharge_eq_completedMoment]
  ring

end RHTower
