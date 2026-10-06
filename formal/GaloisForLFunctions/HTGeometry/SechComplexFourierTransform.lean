import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-!
# The Fourier transform of a hyperbolic power at complex frequency

The logistic substitution `v = e^t/(2 cosh t)` turns `∫ (cosh t)^{−s} e^{−izt} dt` into the Euler
Beta integral `B((s−iz)/2, (s+iz)/2)` for every complex frequency with `|Im z| < s`:

`∫ (cosh t)^{−s} e^{−izt} dt = 2^{s−1} Γ((s−iz)/2) Γ((s+iz)/2) / Γ(s)`
(`integral_cosh_rpow_neg_mul_cexp_complex`).

For `s = 1` the reflection formula gives `∫ e^{−izt}/cosh t dt = π / cosh(πz/2)`
(`integral_cexp_div_cosh`), i.e. `∫ e^{aw}/cosh w dw = π/cos(πa/2)` for `|Re a| < 1`.
-/

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.HTGeometry in
/-- The Beta integrand transported by the logistic substitution, at complex frequency. -/
theorem betaIntegrand_logisticVar_complex {s : ℝ} (z : ℂ) (t : ℝ) :
    ((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - z * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + z * Complex.I) / 2) - 1)
      = Complex.exp (-(z * (t : ℂ)) * Complex.I) *
        ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - (s : ℂ)) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
  have hv : (0 : ℝ) < logisticVar t := logisticVar_pos t
  have hv' : (0 : ℝ) < 1 - logisticVar t := one_sub_logisticVar_pos t
  have hcast : (1 : ℂ) - ((logisticVar t : ℝ) : ℂ) = ((1 - logisticVar t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ofReal_cpow_eq_exp hv, ofReal_cpow_eq_exp hv', ofReal_cpow_eq_exp h2c,
    ← Complex.exp_add, log_logisticVar, log_one_sub_logisticVar]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

open _root_.HTGeometry in
/-- **The Fourier transform of a hyperbolic power at complex frequency** `|Im z| < s`. -/
theorem integral_cosh_rpow_neg_mul_cexp_complex {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : |z.im| < s) :
    (∫ t : ℝ, (((Real.cosh t) ^ (-s) : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ)) * Complex.I))
      = ((2 : ℝ) ^ (s - 1) : ℝ) *
        (Complex.Gamma (((s : ℂ) - z * Complex.I) / 2) *
          Complex.Gamma (((s : ℂ) + z * Complex.I) / 2) / Complex.Gamma (s : ℂ)) := by
  have hinj : Set.InjOn logisticVar Set.univ :=
    Set.injOn_of_injective logisticVar_strictMono.injective
  have hderiv : ∀ t ∈ Set.univ,
      HasDerivWithinAt logisticVar (1 / (2 * Real.cosh t ^ 2)) Set.univ t :=
    fun t _ => (hasDerivAt_logisticVar t).hasDerivWithinAt
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hderiv hinj
    (fun v : ℝ => ((v : ℝ) : ℂ) ^ ((((s : ℂ) - z * Complex.I) / 2) - 1) *
      ((1 : ℂ) - ((v : ℝ) : ℂ)) ^ ((((s : ℂ) + z * Complex.I) / 2) - 1))
  rw [logisticVar_image_univ] at hchange
  have hpt : ∀ t : ℝ, |1 / (2 * Real.cosh t ^ 2)| •
      (((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - z * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + z * Complex.I) / 2) - 1))
      = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) * ((((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-(z * (t : ℂ)) * Complex.I)) := by
    intro t
    have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
    have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
    rw [betaIntegrand_logisticVar_complex z t, abs_of_pos (by positivity), Complex.real_smul]
    have hsplit : ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - (s : ℂ))
        = (((2 : ℝ) ^ (2 - s) : ℝ) : ℂ) * (((Real.cosh t ^ (2 - s) : ℝ)) : ℂ) := by
      rw [show ((2 : ℂ) - (s : ℂ)) = (((2 - s : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow h2c.le, Real.mul_rpow (by norm_num) hc.le]
      push_cast
      ring
    rw [hsplit]
    have hcosh : ((Real.cosh t ^ (2 - s) : ℝ) : ℂ)
        = (((Real.cosh t) ^ (-s) : ℝ) : ℂ) * (((Real.cosh t ^ (2 : ℝ) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hc]
      congr 2
      ring
    have hsq : (Real.cosh t ^ (2 : ℝ) : ℝ) = Real.cosh t ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have htwo : ((2 : ℝ) ^ (2 - s) : ℝ) = ((2 : ℝ) ^ (1 - s) : ℝ) * 2 := by
      rw [show (2 : ℝ) - s = (1 - s) + 1 by ring, Real.rpow_add (by norm_num)]
      norm_num
    rw [hcosh, hsq, htwo]
    have hcne : ((Real.cosh t : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hc.ne'
    have hcne' : Complex.cosh (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_cosh]
      exact hcne
    push_cast
    field_simp
  have hfun : (fun t : ℝ => |1 / (2 * Real.cosh t ^ 2)| •
      (((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - z * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + z * Complex.I) / 2) - 1)))
      = fun t : ℝ => (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) * ((((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-(z * (t : ℂ)) * Complex.I)) := funext hpt
  rw [MeasureTheory.setIntegral_univ, hfun, MeasureTheory.integral_const_mul,
    ← betaIntegral_eq_setIntegral] at hchange
  have hzre1 : (z * Complex.I).re = -z.im := by simp
  have hare : (0 : ℝ) < (((s : ℂ) - z * Complex.I) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.sub_re, hzre1, Complex.ofReal_re]
    have := (abs_lt.1 hz).1
    linarith
  have hbre : (0 : ℝ) < (((s : ℂ) + z * Complex.I) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re, hzre1, Complex.ofReal_re]
    have := (abs_lt.1 hz).2
    linarith
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hare hbre
  have hsum : (((s : ℂ) - z * Complex.I) / 2) + (((s : ℂ) + z * Complex.I) / 2)
      = (s : ℂ) := by ring
  rw [hsum] at hbeta
  have hGne : Complex.Gamma (s : ℂ) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n => ?_
    intro h
    have hre : ((s : ℂ)).re = (-(n : ℂ)).re := by rw [h]
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmul : ((2 : ℝ) ^ (s - 1) : ℝ) * ((2 : ℝ) ^ (1 - s) : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hB : Complex.betaIntegral (((s : ℂ) - z * Complex.I) / 2)
      (((s : ℂ) + z * Complex.I) / 2)
      = Complex.Gamma (((s : ℂ) - z * Complex.I) / 2) *
        Complex.Gamma (((s : ℂ) + z * Complex.I) / 2) / Complex.Gamma (s : ℂ) := by
    rw [eq_div_iff hGne]
    exact (mul_comm _ _).trans hbeta.symm
  rw [hB] at hchange
  rw [hchange, ← mul_assoc, ← Complex.ofReal_mul, hmul]
  simp

/-- **`∫ e^{−izt}/cosh t dt = π / cosh(πz/2)`** for `|Im z| < 1`. -/
theorem integral_cexp_div_cosh {z : ℂ} (hz : |z.im| < 1) :
    ∫ t : ℝ, Complex.exp (-(z * (t : ℂ)) * Complex.I) / (Real.cosh t : ℂ) =
      (Real.pi : ℂ) / Complex.cosh (Real.pi * z / 2) := by
  have h := integral_cosh_rpow_neg_mul_cexp_complex (s := 1) one_pos (z := z) (by simpa using hz)
  have e1 : (fun t : ℝ => (((Real.cosh t) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(z * (t : ℂ)) * Complex.I)) =
      fun t : ℝ => Complex.exp (-(z * (t : ℂ)) * Complex.I) / (Real.cosh t : ℂ) := by
    funext t
    rw [Real.rpow_neg_one, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  rw [e1] at h
  rw [h]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((((1 : ℝ) : ℂ) - z * Complex.I) / 2)
  rw [show (1 : ℂ) - ((((1 : ℝ) : ℂ) - z * Complex.I) / 2) = (((1 : ℝ) : ℂ) + z * Complex.I) / 2 by
    push_cast; ring] at hrefl
  rw [hrefl]
  have hs : Complex.sin (Real.pi * ((((1 : ℝ) : ℂ) - z * Complex.I) / 2)) =
      Complex.cosh (Real.pi * z / 2) := by
    rw [show (Real.pi : ℂ) * ((((1 : ℝ) : ℂ) - z * Complex.I) / 2) =
        Real.pi / 2 - (Real.pi * z / 2) * Complex.I by push_cast; ring,
      Complex.sin_pi_div_two_sub, Complex.cos_mul_I]
  rw [hs]
  simp

end

end GaloisForLFunctions.HTGeometry
