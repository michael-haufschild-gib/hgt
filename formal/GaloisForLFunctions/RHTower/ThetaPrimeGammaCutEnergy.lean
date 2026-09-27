import GaloisForLFunctions.RHTower.ThetaGammaPolarCrossingExchange
import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherBoundary

/-!
# Strict positivity of the full arithmetic single-cut energy

Subtracting the literal continuous crossing current from the complete prime
crossing current cancels the Gamma/pole exchange. The remaining derivative is
the actual multiplication source `-2*x*k(x)^2`. Both currents vanish at the
infinite boundary, so their difference is exactly a theta tail integral.

This proves positivity for every individual threshold cut. Positivity of
mixed cut combinations is a stronger condition and is not asserted here.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace RHTower.ThetaSourceWard

def thetaPrimeGammaCutEnergy (x : ℝ) : ℝ :=
  (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x).re -
    thetaGammaPolarCrossingCurrent thetaCuspTiltSource x

/-- The complete discrete-continuous exchange leaves exactly the multiplication source. -/
theorem hasDerivAt_thetaPrimeGammaCutEnergy (x : ℝ) :
    HasDerivAt thetaPrimeGammaCutEnergy (-(2 * x * thetaCuspFullSource x ^ 2)) x := by
  have hp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x)
  have h := hp.sub (hasDerivAt_thetaGammaPolarCrossingCurrent x)
  convert! h using 1
  simp only [Complex.reCLM_apply, completeTheta_primeShiftWard_balance, Complex.sub_re,
    pow_two, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem continuous_thetaPrimeGammaCutEnergy : Continuous thetaPrimeGammaCutEnergy :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaPrimeGammaCutEnergy x).continuousAt

theorem tendsto_thetaPrimeGammaCutEnergy_atTop : Tendsto thetaPrimeGammaCutEnergy atTop (𝓝 0) := by
  have hp := Complex.continuous_re.tendsto (0 : ℂ) |>.comp
    (tendsto_fullPrimeShiftNoetherCurrent_atTop thetaCuspTiltSource thetaCuspTiltSource)
  have h := hp.sub (tendsto_thetaGammaPolarCrossingCurrent_atTop thetaCuspTiltSource)
  convert! h using 1
  simp only [Complex.zero_re, sub_self]

theorem integrable_thetaCutMoment : Integrable (fun x : ℝ => 2 * x * thetaCuspFullSource x ^ 2) := by
  have h₁ : Integrable (fun x : ℝ => x * thetaCuspFullSource x) := by
    simpa only [pow_one, zero_mul, Complex.exp_zero, mul_one, thetaCuspTiltSource_k,
      RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using (thetaCuspTiltSource.integrable_mul_exp 0 1).re
  have h₂ : Integrable (fun x : ℝ => (x * thetaCuspFullSource x) * thetaCuspFullSource x) := by
    apply h₁.mul_bdd (c := thetaCuspDerivativeExpConstant 0)
      contDiff_thetaCuspFullSource.continuous.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using abs_theta_le_const x
  simpa only [pow_two, mul_assoc] using h₂.const_mul 2

/-- An exact conservation identity with the continuous current given by its literal shift integral. -/
theorem thetaPrimeGammaCutEnergy_conservation (x : ℝ) :
    thetaPrimeGammaCutEnergy x + (∫ t in (0 : ℝ)..x, 2 * t * thetaCuspFullSource t ^ 2) =
      thetaPrimeGammaCutEnergy 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_thetaPrimeGammaCutEnergy t)
    integrable_thetaCutMoment.neg.intervalIntegrable (a := (0 : ℝ)) (b := x)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The single-cut arithmetic energy is an exact absolutely convergent theta tail. -/
theorem thetaPrimeGammaCutEnergy_eq_tail (x : ℝ) :
    thetaPrimeGammaCutEnergy x = ∫ t in Ioi x, 2 * t * thetaCuspFullSource t ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hasDerivAt_thetaPrimeGammaCutEnergy t)
    integrable_thetaCutMoment.neg.integrableOn tendsto_thetaPrimeGammaCutEnergy_atTop (a := x)
  rw [integral_neg, zero_sub] at h
  exact (neg_inj.mp h).symm

theorem thetaPrimeGammaCutEnergy_neg (x : ℝ) :
    thetaPrimeGammaCutEnergy (-x) = thetaPrimeGammaCutEnergy x := by
  have hd (t : ℝ) : HasDerivAt
      (fun y => thetaPrimeGammaCutEnergy (-y) - thetaPrimeGammaCutEnergy y) 0 t := by
    convert! ((hasDerivAt_thetaPrimeGammaCutEnergy (-t)).comp t (hasDerivAt_id t).neg).sub
      (hasDerivAt_thetaPrimeGammaCutEnergy t) using 1
    rw [thetaCuspFullSource_neg]
    ring
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) x 0
  simp only [neg_zero, sub_self] at h
  exact sub_eq_zero.mp h

private theorem cutEnergy_pos_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < thetaPrimeGammaCutEnergy x := by
  rw [thetaPrimeGammaCutEnergy_eq_tail]
  have hp (t : ℝ) (ht : t ∈ Ioi x) : 0 < 2 * t * thetaCuspFullSource t ^ 2 :=
    mul_pos (mul_pos zero_lt_two (hx.trans_lt ht))
      (sq_pos_of_pos (show 0 < thetaCuspFullSource t from thetaCuspTiltSource.pos t))
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hp t ht).le) integrable_thetaCutMoment.integrableOn).mpr
  have he : Function.support (fun t : ℝ => 2 * t * thetaCuspFullSource t ^ 2) ∩ Ioi x = Ioi x := by
    ext t
    exact ⟨fun ht => ht.2, fun ht => ⟨(hp t ht).ne', ht⟩⟩
  rw [he]
  simp

/-- Every real threshold has strictly positive full prime-minus-continuous crossing energy. -/
theorem thetaPrimeGammaCutEnergy_pos (x : ℝ) : 0 < thetaPrimeGammaCutEnergy x := by
  rcases le_total 0 x with hx | hx
  · exact cutEnergy_pos_nonneg hx
  · simpa only [thetaPrimeGammaCutEnergy_neg] using
      cutEnergy_pos_nonneg (x := -x) (neg_nonneg.mpr hx)

theorem thetaGammaPolarCrossingCurrent_lt_prime (x : ℝ) :
    thetaGammaPolarCrossingCurrent thetaCuspTiltSource x <
      (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x).re :=
  sub_pos.mp (thetaPrimeGammaCutEnergy_pos x)

end RHTower.ThetaSourceWard
