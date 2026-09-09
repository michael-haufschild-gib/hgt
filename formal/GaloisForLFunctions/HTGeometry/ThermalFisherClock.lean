import GaloisForLFunctions.HTGeometry.ThermalAmplificationFluctuations

/-!
# Fisher time of the complete thermal occupation law

The accumulated distinguishability of arXiv:2605.03958, equation (12),
applied to the corpus's infinite geometric radiation distribution. The clock
is the hyperbolic radial coordinate of its coherent-state label. Every scale
is admissible because the occupation ratio is `exp (-exp tau)`.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Hyperbolic radial coordinate of the thermal coherent label. -/
def radiationFisherClock (tau : ℝ) : ℝ :=
  Real.log (1 + coherentRadius tau) - Real.log (1 - coherentRadius tau)

theorem coherentRadius_hasDerivAt (tau : ℝ) :
    HasDerivAt coherentRadius (-Real.exp tau * coherentRadius tau / 2) tau := by
  have h := (thermalRatio_hasDerivAt tau).sqrt (thermalRatio_pos tau).ne'
  apply h.congr_deriv
  change -Real.exp tau * thermalRatio tau / (2 * coherentRadius tau) = _
  rw [← coherentRadius_sq tau]
  field_simp [(coherentRadius_pos tau).ne']

/-- Square-root Fisher speed comes from the full infinite squared-score sum. -/
theorem radiationFisherClock_speed (tau : ℝ) :
    Real.sqrt (radiationNumberFisher tau) =
      Real.exp tau * coherentRadius tau / (1 - thermalRatio tau) := by
  have he : radiationNumberFisher tau =
      (Real.exp tau * coherentRadius tau / (1 - thermalRatio tau)) ^ 2 := by
    rw [radiationNumberFisher_formula, radiationNumberVariance_formula]
    rw [div_pow, mul_pow, coherentRadius_sq]
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos]
  exact div_pos (mul_pos (Real.exp_pos tau) (coherentRadius_pos tau))
    (sub_pos.mpr (thermalRatio_lt_one tau))

/-- Cooling traverses the Fisher clock in the negative direction. -/
theorem radiationFisherClock_hasDerivAt (tau : ℝ) :
    HasDerivAt radiationFisherClock (-Real.sqrt (radiationNumberFisher tau)) tau := by
  have hp : 1 + coherentRadius tau ≠ 0 := by linarith [coherentRadius_pos tau]
  have hm : 1 - coherentRadius tau ≠ 0 := (sub_pos.mpr (coherentRadius_lt_one tau)).ne'
  have h := (((coherentRadius_hasDerivAt tau).const_add 1).log hp).sub
    (((hasDerivAt_const tau (1 : ℝ)).sub (coherentRadius_hasDerivAt tau)).log hm)
  apply h.congr_deriv
  rw [radiationFisherClock_speed, ← coherentRadius_sq tau]
  dsimp
  have hq : 1 - coherentRadius tau ^ 2 ≠ 0 := by
    rw [coherentRadius_sq]
    exact (sub_pos.mpr (thermalRatio_lt_one tau)).ne'
  field_simp
  ring

theorem radiationFisherClock_strictAnti : StrictAnti radiationFisherClock := by
  apply strictAnti_of_deriv_neg
  intro tau
  rw [(radiationFisherClock_hasDerivAt tau).deriv]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (radiationNumberFisher_pos tau))

/-- Exact Fisher length of every finite thermal arc, without truncating occupation numbers. -/
theorem radiationFisherClock_integral (a b : ℝ) :
    (∫ tau : ℝ in a..b, Real.sqrt (radiationNumberFisher tau)) =
      radiationFisherClock a - radiationFisherClock b := by
  have hc : Continuous (fun tau => Real.sqrt (radiationNumberFisher tau)) := by
    simp_rw [radiationFisherClock_speed]
    have hq : Continuous thermalRatio := Real.continuous_exp.comp Real.continuous_exp.neg
    exact (Real.continuous_exp.mul hq.sqrt).div (continuous_const.sub hq)
      (fun tau => (sub_pos.mpr (thermalRatio_lt_one tau)).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (fun tau _ => radiationFisherClock_hasDerivAt tau)
    (hc.neg.intervalIntegrable a b)
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem radiationFisherClock_exp (tau : ℝ) :
    Real.exp (radiationFisherClock tau) =
      (1 + coherentRadius tau) / (1 - coherentRadius tau) := by
  rw [radiationFisherClock, Real.exp_sub,
    Real.exp_log (by linarith [coherentRadius_pos tau]),
    Real.exp_log (sub_pos.mpr (coherentRadius_lt_one tau))]

theorem radiationFisherClock_pos (tau : ℝ) : 0 < radiationFisherClock tau := by
  apply Real.exp_lt_exp.mp
  rw [Real.exp_zero, radiationFisherClock_exp]
  apply (lt_div_iff₀ (sub_pos.mpr (coherentRadius_lt_one tau))).mpr
  linarith [coherentRadius_pos tau]

/-- Informational distance reconstructs the coherent radius exactly. -/
theorem radiationFisherClock_recovers_radius (tau : ℝ) :
    (Real.exp (radiationFisherClock tau) - 1) /
      (Real.exp (radiationFisherClock tau) + 1) = coherentRadius tau := by
  rw [radiationFisherClock_exp]
  field_simp [(sub_pos.mpr (coherentRadius_lt_one tau)).ne']
  ring

theorem coherentRadius_exp (tau : ℝ) :
    coherentRadius tau = Real.exp (-Real.exp tau / 2) := by
  have he : thermalRatio tau = Real.exp (-Real.exp tau / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    unfold thermalRatio
    congr 1
    ring
  rw [coherentRadius, he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Logarithmic thermal scale reconstructed from the Fisher clock. -/
def radiationFisherClockReadout (s : ℝ) : ℝ :=
  Real.log (-2 * Real.log ((Real.exp s - 1) / (Real.exp s + 1)))

theorem radiationFisherClock_calibration (tau : ℝ) :
    radiationFisherClockReadout (radiationFisherClock tau) = tau := by
  rw [radiationFisherClockReadout, radiationFisherClock_recovers_radius,
    coherentRadius_exp, Real.log_exp]
  convert Real.log_exp tau using 1
  congr 1
  ring

/-- The same clock is obtained from the actual scattering amplification amplitude. -/
theorem radiationFisherClock_scattering (e tau : ℝ) :
    Real.sqrt (-Real.exp tau * deriv (thermalStepReflection e) tau) =
      -deriv radiationFisherClock tau := by
  rw [← thermalStepReflection_fisher_response,
    (radiationFisherClock_hasDerivAt tau).deriv, neg_neg]

end GaloisForLFunctions.HTGeometry.CPV
