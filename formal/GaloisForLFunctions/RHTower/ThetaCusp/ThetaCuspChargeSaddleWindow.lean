import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeSaddleGeometry

open Complex
open scoped Real

namespace RHTower

noncomputable section

section Factorization

variable {t : ℝ}

/-- **Exact factorization of the saddle-line integrand.**  On the line `Im z = -β` the charge
integrand is `g₀ e^{ReΨ-R₀} · A · e^{iφ} · (1+ε)`, where the unit phase is exactly `1` at `s = 0`. -/
theorem chLine_eq (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) (s : ℝ) :
    chLine t s = (chG0 t : ℂ) * (Real.exp ((chPsi t s).re - chR0 t) : ℂ) *
      (chA t s * Complex.exp (Complex.I * ((chPsi t s).im + 7 * π / 8 : ℝ)) *
        (1 + chargeErr (chV t s))) := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hb : 0 < chB t := lt_of_lt_of_le (by norm_num) (half_le_chB (t := t) (by nlinarith))
  have hv := chV_im_pos ht ht4 hb s
  have hF : thetaGroupBasis 1 (Complex.I * Complex.exp (2 * ((s : ℂ) - (chBeta t : ℂ) * Complex.I)))
      = -chP t s * ((2 : ℂ) ^ 7)⁻¹ * Complex.exp (-(7 * π * Complex.I * chV t s / 4)) *
        (1 + chargeErr (chV t s)) := by
    rw [I_mul_cexp_line ht21, ← one_add_neg_one_div_chV ht ht4, thetaGroupBasis_one_window hv]
    rfl
  have hz : Complex.exp (((s : ℂ) - (chBeta t : ℂ) * Complex.I) / 2) =
      (Real.exp (s / 2) : ℂ) * Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hΨ : Complex.exp (-Complex.I * (chU t : ℂ) * (s : ℂ)) *
      Complex.exp (-(7 * π * Complex.I * chV t s / 4)) =
      (Real.exp (chPsi t s).re : ℂ) * Complex.exp (Complex.I * ((chPsi t s).im + 7 * π / 8 : ℝ)) *
        Complex.exp (-Complex.I * ((7 * π / 8 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * (chU t : ℂ) * (s : ℂ) + -(7 * π * Complex.I * chV t s / 4) = chPsi t s by
      unfold chPsi; ring]
    conv_lhs => rw [← Complex.re_add_im (chPsi t s)]
    rw [Complex.exp_add, ← Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  have key : Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((7 * π / 8 : ℝ) : ℂ)) =
      -Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * ((chBeta t / 2 : ℝ) : ℂ) + -Complex.I * ((7 * π / 8 : ℝ) : ℂ) =
      Complex.I * ((chTheta t / 2 : ℝ) : ℂ) - (π : ℂ) * Complex.I by
      unfold chBeta; push_cast; ring]
    rw [Complex.exp_sub, Complex.exp_pi_mul_I]; ring
  have hp : ((chP0 t : ℝ) : ℂ) * ((chP0 t : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr chP0_pos.ne')
  have hE : (Real.exp ((chPsi t s).re - chR0 t) : ℂ) * (Real.exp (chR0 t) : ℂ) =
      (Real.exp (chPsi t s).re : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  unfold chLine chargeTailC
  rw [hF, hz]
  unfold chG0 chA
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]
  set Es : ℂ := (Real.exp (s / 2) : ℂ)
  set Cb : ℂ := Complex.exp (-Complex.I * ((chBeta t / 2 : ℝ) : ℂ))
  set C7 : ℂ := Complex.exp (-Complex.I * ((7 * π / 8 : ℝ) : ℂ))
  set Ct : ℂ := Complex.exp (Complex.I * ((chTheta t / 2 : ℝ) : ℂ))
  set Cp : ℂ := Complex.exp (Complex.I * ((chPsi t s).im + 7 * π / 8 : ℝ))
  set EP : ℂ := (Real.exp (chPsi t s).re : ℂ)
  set ER : ℂ := (Real.exp (chR0 t) : ℂ)
  set Ed : ℂ := (Real.exp ((chPsi t s).re - chR0 t) : ℂ)
  set pp : ℂ := ((chP0 t : ℝ) : ℂ)
  set X : ℂ := Complex.exp (-Complex.I * (chU t : ℂ) * (s : ℂ))
  set Y : ℂ := Complex.exp (-(7 * π * Complex.I * chV t s / 4))
  set P : ℂ := chP t s
  set ε : ℂ := chargeErr (chV t s)
  linear_combination (-(1 / 256) * Es * Cb * P * (1 + ε)) * hΨ +
    (-(1 / 256) * Es * P * (1 + ε) * EP * Cp) * key +
    (-(1 / 256) * Es * P * (1 + ε) * Cp * Ct * ER * Ed) * hp +
    (-(1 / 256) * Es * P * (1 + ε) * Cp * Ct) * hE

/-- On the window the integrand is dominated by the Gaussian envelope. -/
theorem norm_chLine_le_window (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 160) {s : ℝ}
    (hs : |s| ≤ 2 * t ^ 2) :
    ‖chLine t s‖ ≤ 9 / 8 * (chG0 t * Real.exp ((chPsi t s).re - chR0 t)) := by
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  rw [chLine_eq ht (by linarith)]
  have hε := norm_chargeErr_le (four_le_chV_im ht ht2 hs)
  have hA := norm_chA_le_one ht ht4 s
  have hG : 0 ≤ chG0 t := by unfold chG0; have := chP0_pos (t := t); positivity
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG, abs_of_pos (Real.exp_pos _)]
  have hc : ‖Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hc, mul_one]
  have h1 : ‖1 + chargeErr (chV t s)‖ ≤ 9 / 8 := by
    refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
  have hE := Real.exp_pos ((chPsi t s).re - chR0 t)
  calc chG0 t * Real.exp ((chPsi t s).re - chR0 t) * (‖chA t s‖ * ‖1 + chargeErr (chV t s)‖)
      ≤ chG0 t * Real.exp ((chPsi t s).re - chR0 t) * (1 * (9 / 8)) := by
        gcongr
    _ = 9 / 8 * (chG0 t * Real.exp ((chPsi t s).re - chR0 t)) := by ring

/-- **Positivity of the integrand in the saddle core.** -/
theorem half_le_re_chLine_core (ht : 0 < t) (ht0 : t ≤ 1 / 1000000000) {s : ℝ}
    (hs : |s| ≤ 144 * t ^ 3) :
    chG0 t * Real.exp ((chPsi t s).re - chR0 t) / 2 ≤ (chLine t s).re := by
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht2 : t ^ 2 ≤ 1 / 160 := by nlinarith
  have hts : t ^ 3 ≤ t := by nlinarith [pow_pos ht 2]
  have hs2 : |s| ≤ 2 * t ^ 2 := by nlinarith [pow_pos ht 2]
  have hs12 : |s| ≤ 1 / 2 := by nlinarith
  rw [chLine_eq ht (by linarith)]
  set U : ℂ := chA t s * Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ)) *
    (1 + chargeErr (chV t s)) with hU
  have hε := norm_chargeErr_le (four_le_chV_im ht ht2 hs2)
  have hAd := norm_chA_sub_one_le ht ht1 hs12
  have hφ := abs_chPhi_le ht ht1 hs12
  -- the three small quantities
  have hA8 : ‖chA t s - 1‖ ≤ 1 / 8 := by
    refine le_trans hAd ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos ht 2, pow_pos ht 3]
  have hφ16 : |(chPsi t s).im + 7 * π / 8| ≤ 1 / 16 := by
    refine le_trans hφ ?_
    rw [div_le_iff₀ (by positivity)]
    have h3 : |s| ^ 3 ≤ (144 * t ^ 3) ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hs 3
    nlinarith [pow_pos ht 8, pow_pos ht 9]
  have hexp1 : ‖Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ)) - 1‖ ≤ 1 / 8 := by
    have h := Complex.norm_exp_sub_one_le (x := Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ))
      (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; linarith)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hc : ‖Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hA1 := norm_chA_le_one ht ht4 s
  have hU1 : ‖U - 1‖ ≤ 1 / 2 := by
    have e : U - 1 = (chA t s - 1) * Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ))
        * (1 + chargeErr (chV t s)) +
        (Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ)) - 1) *
          (1 + chargeErr (chV t s)) + chargeErr (chV t s) := by rw [hU]; ring
    have h1e : ‖1 + chargeErr (chV t s)‖ ≤ 9 / 8 := by
      refine le_trans (norm_add_le _ _) ?_; rw [norm_one]; linarith
    rw [e]
    calc _ ≤ ‖(chA t s - 1) * Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ))
            * (1 + chargeErr (chV t s))‖ +
          ‖(Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ)) - 1) *
            (1 + chargeErr (chV t s))‖ + ‖chargeErr (chV t s)‖ := norm_add₃_le
      _ = ‖chA t s - 1‖ * 1 * ‖1 + chargeErr (chV t s)‖ +
          ‖Complex.exp (Complex.I * (((chPsi t s).im + 7 * π / 8 : ℝ) : ℂ)) - 1‖ *
            ‖1 + chargeErr (chV t s)‖ + ‖chargeErr (chV t s)‖ := by
          rw [norm_mul, norm_mul, norm_mul, hc]
      _ ≤ 1 / 8 * 1 * (9 / 8) + 1 / 8 * (9 / 8) + 1 / 8 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hReU : 1 / 2 ≤ U.re := by
    have h := Complex.abs_re_le_norm (U - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    have := abs_le.mp (le_trans h hU1)
    linarith [this.1]
  have hG : 0 ≤ chG0 t := by unfold chG0; have := chP0_pos (t := t); positivity
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hpos : 0 ≤ chG0 t * Real.exp ((chPsi t s).re - chR0 t) :=
    mul_nonneg hG (Real.exp_pos _).le
  nlinarith

end Factorization

end

end RHTower
