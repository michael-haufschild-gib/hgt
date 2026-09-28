import GaloisForLFunctions.RHTower.CCMCoherentSignedMomentGammaControl
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileStieltjesCrossing

/-!
# The moment charge as an actual arithmetic action

At the physical cutoff `floor(exp H)+1`, the charge is the signed integral of
the completed critical-Mellin error after its exact deterministic threshold is
removed. The Gamma charge estimate therefore controls this actual arithmetic
action, with no finite-head crossing correction or terminal-order premise.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

theorem ccmActualHeadSignedMomentCharge_eq_quadraticProfile (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentCharge T N = Real.pi *
      ((∑ n ∈ Finset.range N, criticalMellinAtomWeight n*(T^2-(Real.log n)^2)) -
        ∫ h in (0 : ℝ)..T, Real.exp (h/2)*(T^2-h^2)) := by
  have h0 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*h^2) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi : (∫ h in (0 : ℝ)..T, Real.exp (h/2)*(T^2-h^2)) =
      (2*Real.exp (T/2)-2)*T^2 - ∫ h in (0 : ℝ)..T, Real.exp (h/2)*h^2 := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (h0.mul_const _) h2,
      intervalIntegral.integral_mul_const, intervalIntegral_exp_half_eq]
    simp only [zero_div, Real.exp_zero, mul_one]
  rw [ccmActualHeadSignedMomentCharge_eq_completedMoment, hi]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  unfold ccmOutgoingPrimeCumulative
  ring

private theorem quadratic_pairing_real (H : NNReal) :
    (criticalMellinStieltjesPairing ((H : ℝ)/2)
      (fun h : ℝ => (((H : ℝ)^2-h^2 : ℝ) : ℂ))).re =
      (∫ h in (0 : ℝ)..(H : ℝ), 2*Real.cosh (h/2)*((H : ℝ)^2-h^2)) -
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (H : ℝ))),
          criticalMellinAtomWeight n*((H : ℝ)^2-(Real.log n)^2) := by
  unfold criticalMellinStieltjesPairing
  simp only [show 2*((H : ℝ)/2) = (H : ℝ) by ring]
  have he : (fun h : ℝ => (((H : ℝ)^2-h^2 : ℝ) : ℂ)*(2*Real.cosh (h/2) : ℂ)) =
      fun h => ((2*Real.cosh (h/2)*((H : ℝ)^2-h^2) : ℝ) : ℂ) := by
    funext h
    push_cast
    ring
  rw [he, integral_complex_ofReal]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [intervalIntegral.integral_of_le H.coe_nonneg]

private theorem quadratic_pairing_action (H : NNReal) :
    (∫ h in (0 : ℝ)..(H : ℝ), 2*Real.cosh (h/2)*((H : ℝ)^2-h^2)) -
        (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (H : ℝ))),
          criticalMellinAtomWeight n*((H : ℝ)^2-(Real.log n)^2)) =
      2*(∫ h in (0 : ℝ)..(H : ℝ), h*criticalMellinCompletedError h) := by
  have h := congrArg Complex.re (criticalMellinStieltjesPairing_quadraticNonnegativeTimeCutoff H)
  rw [quadratic_pairing_real] at h
  have he : (fun x : ℝ => (criticalMellinCompletedError x : ℂ)*((-2*x : ℝ) : ℂ)) =
      fun x => (((-2)*(x*criticalMellinCompletedError x) : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  rw [he, integral_complex_ofReal, Complex.neg_re, Complex.ofReal_re, integral_const_mul] at h
  rw [intervalIntegral.integral_of_le (μ := volume)
    (f := fun h : ℝ => h*criticalMellinCompletedError h) H.coe_nonneg]
  linarith only [h]

/-- The physical-head charge is the exact threshold-centered arithmetic action. -/
theorem ccmActualTimeSignedMomentCharge_eq_completedErrorAction (H : NNReal) :
    ccmActualHeadSignedMomentCharge (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1) =
      -2*Real.pi*(∫ h in (0 : ℝ)..(H : ℝ),
        h*(criticalMellinCompletedError h-2*(1-Real.exp (-h/2)))) := by
  have hp := ccmActualHeadSignedMomentCharge_eq_quadraticProfile (H : ℝ)
    (Nat.floor (Real.exp (H : ℝ))+1)
  rw [sum_range_succ_criticalMellinAtomWeight_mul_eq_Icc] at hp
  have ha := quadratic_pairing_action H
  have hplus : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*((H : ℝ)^2-h^2))
      volume 0 (H : ℝ) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hminus : IntervalIntegrable (fun h : ℝ => Real.exp (-h/2)*((H : ℝ)^2-h^2))
      volume 0 (H : ℝ) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsplit : (∫ h in (0 : ℝ)..(H : ℝ), Real.exp (h/2)*((H : ℝ)^2-h^2)) +
      ccmOutgoingQuantileQuadraticArchimedeanLeakage (H : ℝ) =
      ∫ h in (0 : ℝ)..(H : ℝ), 2*Real.cosh (h/2)*((H : ℝ)^2-h^2) := by
    rw [ccmOutgoingQuantileQuadraticArchimedeanLeakage, ← intervalIntegral.integral_add hplus hminus]
    apply intervalIntegral.integral_congr
    intro h _
    dsimp only
    rw [Real.cosh_eq, show -h/2 = -(h/2) by ring]
    ring
  rw [ccmOutgoingQuantileQuadraticArchimedeanLeakage_eq_thresholdAction] at hsplit
  have hE := (intervalIntegrable_criticalMellinCompletedError_nonnegativeTime H).continuousOn_mul
    (show ContinuousOn (fun h : ℝ => h) (uIcc 0 (H : ℝ)) from continuous_id.continuousOn)
  have hE' : IntervalIntegrable (fun h : ℝ => h*criticalMellinCompletedError h) volume 0 (H : ℝ) := by
    simpa only [mul_comm] using hE
  have hb : IntervalIntegrable (fun h : ℝ => h*(2*(1-Real.exp (-h/2)))) volume 0 (H : ℝ) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have he : (∫ h in (0 : ℝ)..(H : ℝ),
      h*(criticalMellinCompletedError h-2*(1-Real.exp (-h/2)))) =
      (∫ h in (0 : ℝ)..(H : ℝ), h*criticalMellinCompletedError h) -
        ∫ h in (0 : ℝ)..(H : ℝ), h*(2*(1-Real.exp (-h/2))) := by
    rw [← intervalIntegral.integral_sub hE' hb]
    apply intervalIntegral.integral_congr
    intro h _
    ring
  rw [he]
  linear_combination hp - Real.pi*ha - Real.pi*hsplit

/-- Actual completed-error action obeys the uniform Gamma-capacity estimate. -/
theorem sq_ccmActualTimeCompletedErrorAction_le_gammaEnergy (H : NNReal) :
    (2*Real.pi)^2 * (∫ h in (0 : ℝ)..(H : ℝ),
      h*(criticalMellinCompletedError h-2*(1-Real.exp (-h/2))))^2 ≤
      ccmGammaSignedMomentCapacity * ccmActualHeadSignedMomentGammaEnergy (H : ℝ)
        (Nat.floor (Real.exp (H : ℝ))+1) := by
  have h := sq_ccmActualHeadSignedMomentCharge_le_capacity (H : ℝ)
    (Nat.floor (Real.exp (H : ℝ))+1)
  rw [ccmActualTimeSignedMomentCharge_eq_completedErrorAction] at h
  convert h using 1
  ring

/-- The deterministic threshold removes exactly the two exponential baseline terms. -/
theorem criticalMellinThresholdCenteredError_eq_chebyshevVolterra (h : NNReal) :
    criticalMellinCompletedError (h : ℝ)-2*(1-Real.exp (-(h : ℝ)/2)) =
      -(1+criticalMellinNormalizedChebyshevError (h : ℝ) +
        (1/2 : ℝ)*(∫ u in Ioc (0 : ℝ) (h : ℝ), criticalMellinNormalizedChebyshevError u)) := by
  rw [criticalMellinCompletedError_eq_volterraPotential h.coe_nonneg,
    criticalMellinChebyshevVolterraPotential, ← Real.exp_half, div_eq_mul_inv, ← Real.exp_neg,
    show -(h : ℝ)/2 = -((h : ℝ)/2) by ring]
  ring

/-- The charge is a concrete Volterra moment of the square-root-normalized Chebyshev remainder. -/
theorem ccmActualTimeSignedMomentCharge_eq_chebyshevVolterra (H : NNReal) :
    ccmActualHeadSignedMomentCharge (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1) =
      2*Real.pi*(∫ h in (0 : ℝ)..(H : ℝ), h*(1+criticalMellinNormalizedChebyshevError h +
        (1/2 : ℝ)*(∫ u in Ioc (0 : ℝ) h, criticalMellinNormalizedChebyshevError u))) := by
  rw [ccmActualTimeSignedMomentCharge_eq_completedErrorAction,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro h hh
  rw [uIcc_of_le H.coe_nonneg] at hh
  have ht := criticalMellinThresholdCenteredError_eq_chebyshevVolterra (NNReal.mk h hh.1)
  simp only [NNReal.coe_mk] at ht
  dsimp only
  rw [ht]
  ring

theorem sq_ccmActualTimeChebyshevVolterraAction_le_gammaEnergy (H : NNReal) :
    (2*Real.pi)^2 * (∫ h in (0 : ℝ)..(H : ℝ), h*(1+criticalMellinNormalizedChebyshevError h +
      (1/2 : ℝ)*(∫ u in Ioc (0 : ℝ) h, criticalMellinNormalizedChebyshevError u)))^2 ≤
      ccmGammaSignedMomentCapacity * ccmActualHeadSignedMomentGammaEnergy (H : ℝ)
        (Nat.floor (Real.exp (H : ℝ))+1) := by
  have h := sq_ccmActualHeadSignedMomentCharge_le_capacity (H : ℝ)
    (Nat.floor (Real.exp (H : ℝ))+1)
  rw [ccmActualTimeSignedMomentCharge_eq_chebyshevVolterra, mul_pow] at h
  exact h

end RHTower
