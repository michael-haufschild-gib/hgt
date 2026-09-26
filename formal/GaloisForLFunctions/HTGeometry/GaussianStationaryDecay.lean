import GaloisForLFunctions.HTGeometry.GaussianHalfLineMoment

/-!
# A Gaussian obstruction to rapid stationary-phase decay

For `J(t) = integral_0^infinity x^2 exp(-(1-I*t)*x^2) dx`, the exact law is
`norm(J(t))^4 * (1+t^2)^3 = pi^2/256`. Thus a quadratic zero at the stationary
point gives only finite-order decay. In particular, `q^4 * norm(J(q^2))` is
unbounded even when `q` ranges only over positive powers of two.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The square of the twisted second moment has a rational closed form. -/
theorem gaussianHalfMoment_one_twist_sq (t : ℝ) :
    gaussianHalfMoment (1 - Complex.I * t) 1 ^ 2 *
      (1 - Complex.I * t) ^ 3 = (Real.pi : ℂ) / 16 := by
  have hw : 0 < (1 - Complex.I * (t : ℂ)).re := by simp
  have hw0 : (1 - Complex.I * (t : ℂ)) ≠ 0 := by
    intro h
    rw [h] at hw
    exact (lt_irrefl 0) hw
  have hroot : (((Real.pi : ℂ) / (1 - Complex.I * t)) ^ (1 / 2 : ℂ)) ^ 2 =
      (Real.pi : ℂ) / (1 - Complex.I * t) := by
    rw [← Complex.cpow_mul_nat]
    norm_num
  rw [show (1 : ℕ) = 0 + 1 from rfl, gaussianHalfMoment_succ hw,
    gaussianHalfMoment_zero hw]
  simp only [Nat.cast_zero, mul_zero, zero_add, mul_pow, div_pow]
  rw [hroot]
  field_simp
  ring

/-- Exact magnitude of the twisted second moment, without asymptotic error. -/
theorem gaussianHalfMoment_one_twist_norm_four (t : ℝ) :
    ‖gaussianHalfMoment (1 - Complex.I * t) 1‖ ^ 4 * (1 + t ^ 2) ^ 3 =
      Real.pi ^ 2 / 256 := by
  have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) (gaussianHalfMoment_one_twist_sq t)
  have hw : ‖(1 : ℂ) - Complex.I * t‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [pow_two]
  rw [norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le] at h
  norm_num only [norm_ofNat] at h
  calc
    ‖gaussianHalfMoment (1 - Complex.I * t) 1‖ ^ 4 * (1 + t ^ 2) ^ 3 =
        (‖gaussianHalfMoment (1 - Complex.I * t) 1‖ ^ 2 *
          ‖(1 : ℂ) - Complex.I * t‖ ^ 3) ^ 2 := by rw [← hw]; ring
    _ = (Real.pi / 16) ^ 2 := h
    _ = Real.pi ^ 2 / 256 := by ring


/-- Even along dyadic scales, the second moment does not decay to fourth order. -/
theorem gaussianHalfMoment_one_dyadic_not_rapid :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      ((2 : ℝ) ^ n) ^ 4 *
        ‖gaussianHalfMoment (1 - Complex.I * ((2 : ℝ) ^ n) ^ 2) 1‖ ≤ C := by
  rintro ⟨C, hC⟩
  let c : ℝ := Real.pi ^ 2 / 256
  have hc : 0 < c := div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 8 * C ^ 4 / c + 1 from le_add_of_nonneg_left (by positivity))
    (show (1 : ℝ) < 2 by norm_num)
  let q : ℝ := 2 ^ (n + 1)
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hq4 : 1 ≤ q ^ 4 := one_le_pow₀ hq
  have hqle : q ≤ q ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hq (show 1 ≤ 4 by norm_num)
  have hmoment : ‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖ ^ 4 *
      (1 + q ^ 4) ^ 3 = c := by
    have h := gaussianHalfMoment_one_twist_norm_four (q ^ 2)
    rw [Complex.ofReal_pow, ← pow_mul q 2 2] at h
    exact h
  have hCq : q ^ 4 * ‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖ ≤ C := by
    simpa only [q, Complex.ofReal_pow] using hC (n + 1)
  have hbound := pow_le_pow_left₀
    (show 0 ≤ q ^ 4 * ‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖ by positivity)
    hCq 4
  have hphase : (1 + q ^ 4) ^ 3 ≤ (2 * q ^ 4) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hupper : c * q ^ 4 ≤ 8 * C ^ 4 := by
    calc
      c * q ^ 4 = (‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖ ^ 4 *
          (1 + q ^ 4) ^ 3) * q ^ 4 := by rw [hmoment]
      _ ≤ (‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖ ^ 4 *
          (2 * q ^ 4) ^ 3) * q ^ 4 := by gcongr
      _ = 8 * (q ^ 4 * ‖gaussianHalfMoment (1 - Complex.I * q ^ 2) 1‖) ^ 4 := by ring
      _ ≤ 8 * C ^ 4 := mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hsmall : c * q ≤ 8 * C ^ 4 :=
    (mul_le_mul_of_nonneg_left hqle hc.le).trans hupper
  have hlarge := mul_lt_mul_of_pos_left hn hc
  have hvalue : c * (8 * C ^ 4 / c + 1) = 8 * C ^ 4 + c := by
    field_simp
  linarith

end GaloisForLFunctions.HTGeometry

