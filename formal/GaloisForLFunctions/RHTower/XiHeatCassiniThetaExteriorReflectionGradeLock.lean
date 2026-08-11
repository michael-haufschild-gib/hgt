import GaloisForLFunctions.RHTower.HedenmalmThetaXiMassPhaseLinearWeld

/-!
# Exterior theta reflection is a scalar grade lock

Reflecting the safe theta line from `c` to `-c` does not create a second phase equation.
The even Xi-mass test is unchanged after reversing the frequency variable, whereas the
phase-linear theta logarithmic jet is odd.  Consequently the complete reflected wave packet is
the negative of the original packet.  This closes the apparent two-line route to an independent
quadrature before any norm or asymptotic estimate is introduced.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Reflection of the exterior theta parameter, with simultaneous frequency reversal. -/
theorem thetaEsscherResolventParameter_neg_height_neg_frequency
    (c x : ℝ) :
    thetaEsscherResolventParameter (-c) (-x) =
      -thetaEsscherResolventParameter c x := by
  unfold thetaEsscherResolventParameter
  push_cast
  ring

/-- Evenness of the analytic mass test identifies the reflected bottom test after reversing
frequency. -/
theorem xiMassBottomTest_neg_height (a c : ℝ) (tau : ℂ) (x : ℝ) :
    xiMassBottomTest a (-c) tau x = xiMassBottomTest a c tau (-x) := by
  rw [xiMassBottomTest, xiMassBottomTest]
  have harg :
      ((((-x : ℝ) : ℂ) - (c : ℂ) * Complex.I)) =
        -(((x : ℂ) - ((-c : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [harg, xiMassAnalyticTest_neg]

/-- The phase-linear theta row changes sign under exterior-line reflection. -/
theorem pinnedMean_thetaQuantileResolvent_neg_height_neg_frequency
    {c : ℝ} (hc : 1 / 2 ≤ |c|) (x : ℝ) :
    pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter (-c) (-x))
          thetaQuantileCoordinate) =
      -pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter c x)
          thetaQuantileCoordinate) := by
  have hnegc : 1 / 2 ≤ |-c| := by simpa using hc
  have hleft :
      IsUnit (thetaSourcePencil (thetaEsscherResolventParameter (-c) (-x))) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hnegc (-x)
  have hright :
      IsUnit (thetaSourcePencil (thetaEsscherResolventParameter c x)) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hc x
  rw [pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hleft,
    pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hright,
    thetaEsscherResolventParameter_neg_height_neg_frequency,
    logDeriv_XiC_neg]
  ring

/-- Pointwise scalar grade lock: the reflected phase-linear theta integrand is the negative of the
original integrand at reversed frequency. -/
theorem xiMassThetaQuantileResolventIntegrand_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) (x : ℝ) :
    xiMassThetaQuantileResolventIntegrand a (-c) tau x =
      -xiMassThetaQuantileResolventIntegrand a c tau (-x) := by
  rw [xiMassThetaQuantileResolventIntegrand,
    xiMassThetaQuantileResolventIntegrand,
    xiMassBottomTest_neg_height,
    pinnedMean_thetaQuantileResolvent_neg_height_neg_frequency hc]
  ring

/-- **Exterior reflection grade lock.**  The complete reflected theta wave packet is exactly the
negative of the original packet. -/
theorem xiMassThetaQuantileResolventIntegral_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileResolventIntegral a (-c) tau =
      -xiMassThetaQuantileResolventIntegral a c tau := by
  rw [xiMassThetaQuantileResolventIntegral,
    xiMassThetaQuantileResolventIntegral]
  have hpoint :
      xiMassThetaQuantileResolventIntegrand a (-c) tau =
        fun x : ℝ => -xiMassThetaQuantileResolventIntegrand a c tau (-x) := by
    funext x
    exact xiMassThetaQuantileResolventIntegrand_neg_height a hc tau x
  rw [hpoint, MeasureTheory.integral_neg]
  congr 1
  exact MeasureTheory.integral_neg_eq_self
    (xiMassThetaQuantileResolventIntegrand a c tau) volume

/-- The two exterior packets have identically zero sum, so they cannot provide two independent
scalar equations. -/
theorem xiMassThetaQuantileResolventIntegral_exterior_pair_eq_zero
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileResolventIntegral a (-c) tau +
        xiMassThetaQuantileResolventIntegral a c tau = 0 := by
  rw [xiMassThetaQuantileResolventIntegral_neg_height a hc]
  exact neg_add_cancel _

/-- Reflection preserves the packet norm and hence cannot improve its scalar line-bound problem. -/
theorem norm_xiMassThetaQuantileResolventIntegral_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    ‖xiMassThetaQuantileResolventIntegral a (-c) tau‖ =
      ‖xiMassThetaQuantileResolventIntegral a c tau‖ := by
  rw [xiMassThetaQuantileResolventIntegral_neg_height a hc, norm_neg]

end

end RHTower
