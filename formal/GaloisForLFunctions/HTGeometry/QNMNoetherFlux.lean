import GaloisForLFunctions.HTGeometry.ChargedWaveFlux
import GaloisForLFunctions.HTGeometry.QNMPoschlTeller

/-!
# Damped Pöschl--Teller modes and full Noether conservation

Tests the real-frequency Wronskian assumption of arXiv:2608.21406v1,
section 4, against the corpus's actual complex-frequency Pöschl--Teller modes.
Their spatial flux is not constant for an oscillating damped mode. The exact
survivor is Appendix A's full spacetime continuity law: the changing temporal
charge balances the spatial-current derivative, locally and on every finite
interval.

All currents use actual time and space derivatives. The height
`log (2*cosh x)` fixes both normalization and exact exponential time decay.
No conservation, wave-equation, integrability, or boundary-flux premise is
introduced. This does not identify damped QNMs with real-frequency scattering
states or infer superradiant amplification from their spatial current.
-/

noncomputable section
open Complex Filter Polynomial
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The temporal component of the Lorentzian Noether current, using the actual time derivative. -/
def complexTemporalCharge (ψ : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ :=
  -((starRingEnd ℂ) (ψ t x) * deriv (fun u => ψ u x) t).im

theorem qnmConstantMode_spatial_derivative (z : ℂ) (t x : ℝ) :
    HasDerivAt (qnmComplexHyperboloidalWave z 1 t)
      (-z * (Real.tanh x : ℂ) * qnmComplexHyperboloidalWave z 1 t x) x := by
  have h := (hasDerivAt_qnmComplexHyperboloidalProfile z (1 : Polynomial ℂ) x).const_mul
    (Complex.exp (z * (t : ℂ)))
  apply h.congr_deriv
  simp [qnmComplexHyperboloidalWave, qnmComplexHyperboloidalProfile, qnmHyperboloidalDx]
  ring

/-- The current of an actual separated mode, before specializing its complex frequency. -/
theorem qnmConstantMode_radialFlux (z : ℂ) (t x : ℝ) :
    complexRadialFlux (qnmComplexHyperboloidalWave z 1 t) x =
      -z.im * Real.tanh x * ‖qnmComplexHyperboloidalWave z 1 t x‖ ^ (2 : ℕ) := by
  rw [complexRadialFlux, (qnmConstantMode_spatial_derivative z t x).deriv]
  have he : (starRingEnd ℂ) (qnmComplexHyperboloidalWave z 1 t x) *
      (-z * (Real.tanh x : ℂ) * qnmComplexHyperboloidalWave z 1 t x) =
      (-z * (Real.tanh x : ℂ)) *
        ((starRingEnd ℂ) (qnmComplexHyperboloidalWave z 1 t x) * qnmComplexHyperboloidalWave z 1 t x) := by ring
  rw [he, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The temporal charge of the same mode is read from its actual time derivative. -/
theorem qnmConstantMode_temporalCharge (z : ℂ) (t x : ℝ) :
    complexTemporalCharge (qnmComplexHyperboloidalWave z 1) t x =
      -z.im * ‖qnmComplexHyperboloidalWave z 1 t x‖ ^ (2 : ℕ) := by
  rw [complexTemporalCharge, qnmComplexHyperboloidalWave_time_deriv]
  have he : (starRingEnd ℂ) (qnmComplexHyperboloidalWave z 1 t x) *
      (z * qnmComplexHyperboloidalWave z 1 t x) =
      z * ((starRingEnd ℂ) (qnmComplexHyperboloidalWave z 1 t x) * qnmComplexHyperboloidalWave z 1 t x) := by ring
  rw [he, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  ring

/-- The existing height is `log (2 cosh x)`, fixing the exact density normalization. -/
theorem qnmPoschlTeller_norm_square (s t x : ℝ) :
    ‖qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t x‖ ^ (2 : ℕ) =
      2 * Real.cosh x * Real.exp (-t) := by
  rw [norm_qnmPoschlTeller_wave, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * ((qnmHyperboloidalHeight x - t) / 2) = qnmHyperboloidalHeight x - t := by ring
  rw [he, Real.exp_sub, qnmHyperboloidalHeight, Real.exp_log (by positivity : (0 : ℝ) < 2 * Real.cosh x), Real.exp_neg]
  ring

/-- Damped modes have spatially varying current, despite a real barrier potential. -/
theorem qnmPoschlTeller_radialFlux (s t x : ℝ) :
    complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t) x =
      -2 * s * Real.sinh x * Real.exp (-t) := by
  rw [qnmConstantMode_radialFlux, qnmPoschlTeller_norm_square]
  have hi : (qnmPoschlTellerExponent s).im = s := by simp [qnmPoschlTellerExponent]
  rw [hi, Real.tanh_eq_sinh_div_cosh]
  have hn := (Real.cosh_pos x).ne'
  field_simp

theorem qnmPoschlTeller_temporalCharge (s t x : ℝ) :
    complexTemporalCharge (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1) t x =
      -2 * s * Real.cosh x * Real.exp (-t) := by
  rw [qnmConstantMode_temporalCharge, qnmPoschlTeller_norm_square]
  have hi : (qnmPoschlTellerExponent s).im = s := by simp [qnmPoschlTellerExponent]
  rw [hi]
  ring

theorem qnmPoschlTeller_flux_derivative (s t x : ℝ) :
    HasDerivAt (complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t))
      (-2 * s * Real.cosh x * Real.exp (-t)) x := by
  simp only [funext (qnmPoschlTeller_radialFlux s t)]
  exact ((Real.hasDerivAt_sinh x).const_mul (-2 * s)).mul_const (Real.exp (-t))

theorem qnmPoschlTeller_charge_derivative (s t x : ℝ) :
    HasDerivAt (fun u => complexTemporalCharge (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1) u x)
      (2 * s * Real.cosh x * Real.exp (-t)) t := by
  simp only [qnmPoschlTeller_temporalCharge]
  exact (((hasDerivAt_id t).neg).exp.const_mul (-2 * s * Real.cosh x)).congr_deriv (by simp only [Pi.neg_apply, id_eq]; ring)

/-- Appendix A survives as the full spacetime Noether continuity equation. -/
theorem qnmPoschlTeller_noether_continuity (s t x : ℝ) :
    deriv (fun u => complexTemporalCharge (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1) u x) t +
      deriv (complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t)) x = 0 := by
  rw [(qnmPoschlTeller_charge_derivative s t x).deriv, (qnmPoschlTeller_flux_derivative s t x).deriv]
  ring

/-- A zero spatial-flux derivative forces the nonoscillating member of this family. -/
theorem qnmPoschlTeller_flux_derivative_zero_iff (s t x : ℝ) :
    deriv (complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t)) x = 0 ↔ s = 0 := by
  rw [(qnmPoschlTeller_flux_derivative s t x).deriv]
  have hc := (Real.cosh_pos x).ne'
  have he := Real.exp_ne_zero (-t)
  constructor
  · intro h
    have hp : s * (-2 * Real.cosh x * Real.exp (-t)) = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hp).resolve_right (by positivity)
  · rintro rfl
    ring

/-- Noether charge in an arbitrary finite interval. -/
def qnmNoetherBoxCharge (s a b t : ℝ) : ℝ :=
  ∫ x in a..b, complexTemporalCharge (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1) t x

/-- The integrated charge is determined by the actual endpoint currents. -/
theorem qnmNoetherBoxCharge_flux_difference (s a b t : ℝ) :
    qnmNoetherBoxCharge s a b t =
      complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t) b -
        complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t) a := by
  unfold qnmNoetherBoxCharge
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    simpa only [qnmPoschlTeller_temporalCharge] using qnmPoschlTeller_flux_derivative s t x
  · have hc : Continuous (fun x => complexTemporalCharge
        (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1) t x) := by
      simp only [qnmPoschlTeller_temporalCharge]
      exact (continuous_const.mul Real.continuous_cosh).mul continuous_const
    exact hc.intervalIntegrable a b

theorem qnmNoetherBoxCharge_eq (s a b t : ℝ) :
    qnmNoetherBoxCharge s a b t = -2 * s * (Real.sinh b - Real.sinh a) * Real.exp (-t) := by
  rw [qnmNoetherBoxCharge_flux_difference, qnmPoschlTeller_radialFlux, qnmPoschlTeller_radialFlux]
  ring

/-- Integrated Noether conservation: charge change equals incoming minus outgoing flux. -/
theorem qnmNoetherBoxCharge_conservation (s a b t : ℝ) :
    HasDerivAt (qnmNoetherBoxCharge s a b)
      (complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t) a -
        complexRadialFlux (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t) b) t := by
  simp only [funext (qnmNoetherBoxCharge_eq s a b), qnmPoschlTeller_radialFlux]
  apply (((hasDerivAt_id t).neg).exp.const_mul (-2 * s * (Real.sinh b - Real.sinh a))).congr_deriv
  simp only [Pi.neg_apply, id_eq]
  ring

/-- Every finite-interval charge has the exact damping semigroup. -/
theorem qnmNoetherBoxCharge_time_shift (s a b t h : ℝ) :
    qnmNoetherBoxCharge s a b (t + h) = Real.exp (-h) * qnmNoetherBoxCharge s a b t := by
  simp only [qnmNoetherBoxCharge_eq, neg_add, Real.exp_add]
  ring

end GaloisForLFunctions.HTGeometry
