import GaloisForLFunctions.RHTower.SemilocalJacobiMeixnerPollaczekGeneratingFunction
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# Cauchy bound for the Meixner–Pollaczek coefficients `c_m p_m(s)`

On the circle `‖w‖ = 1/4` the generating function `G_s(w) = (1 − iw)^{−1/4+is/2}(1 + iw)^{−1/4−is/2}`
is bounded by `(3/4)^{−1/2} e^{|s|/2}` (the arguments of `1 ∓ iw` are below `1/2` there), so Cauchy's
estimate gives the coefficient bound

`|c_m p_m(s)| ≤ (3/4)^{−1/2} e^{|s|/2} 4^m`.

The exponential rate `1/2` is what makes the two-variable boost series dominated by an integrable
function of the Gamma measure (`e^{|s|} ≪ e^{π|s|/2}`).
-/

open Complex

namespace RHTower

namespace MeixnerPollaczek

open GaloisForLFunctions.HTGeometry

theorem mpExponentPlus_re (s : ℝ) : (mpExponentPlus s).re = -(1 / 4) := by
  simp [mpExponentPlus]

theorem mpExponentPlus_im (s : ℝ) : (mpExponentPlus s).im = s / 2 := by
  simp [mpExponentPlus]

theorem mpExponentMinus_re (s : ℝ) : (mpExponentMinus s).re = -(1 / 4) := by
  simp [mpExponentMinus]

theorem mpExponentMinus_im (s : ℝ) : (mpExponentMinus s).im = -(s / 2) := by
  simp [mpExponentMinus]

theorem three_quarters_le_norm_one_sub_I_mul {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    3 / 4 ≤ ‖1 - I * w‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (I * w)
  rw [norm_one, norm_mul, norm_I, one_mul] at h
  linarith

theorem three_quarters_le_norm_one_add_I_mul {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    3 / 4 ≤ ‖1 + I * w‖ := by
  have h := norm_sub_le (1 + I * w) (I * w)
  rw [add_sub_cancel_right, norm_one, norm_mul, norm_I, one_mul] at h
  linarith

theorem one_sub_I_mul_eq_sub_mul_I (w : ℂ) :
    1 - I * w = ((1 + w.im : ℝ) : ℂ) - (w.re : ℂ) * I := by
  apply Complex.ext <;> simp

theorem one_add_I_mul_eq_sub_mul_I (w : ℂ) :
    1 + I * w = ((1 - w.im : ℝ) : ℂ) - ((-w.re : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp <;> ring

/-- The argument of `A − B i` (with `A > 0`) is bounded by the argument of its inverse. -/
theorem abs_arg_sub_mul_I_lt {A B t : ℝ} (hA : 0 < A) (hB : |B| < t * A) :
    |Complex.arg ((A : ℂ) - B * I)| < t := by
  have h := abs_arg_inv_sub_mul_I_lt hA hB
  have hre : 0 < ((A : ℂ) - B * I).re := by simp [hA]
  have hne : Complex.arg ((A : ℂ) - B * I) ≠ Real.pi := by
    intro hpi
    have := Complex.arg_eq_pi_iff.mp hpi
    linarith [this.1]
  rw [Complex.arg_inv, if_neg hne, abs_neg] at h
  exact h

theorem abs_arg_one_sub_I_mul_lt {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    |(1 - I * w).arg| < 1 / 2 := by
  have him := abs_im_le_norm w
  have hre := abs_re_le_norm w
  have hA : 0 < 1 + w.im := by linarith [(abs_le.mp (him.trans hw)).1]
  have hB : |w.re| < 1 / 2 * (1 + w.im) := by
    have := (abs_le.mp (him.trans hw)).1
    linarith [hre.trans hw]
  rw [one_sub_I_mul_eq_sub_mul_I]
  exact abs_arg_sub_mul_I_lt hA hB

theorem abs_arg_one_add_I_mul_lt {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    |(1 + I * w).arg| < 1 / 2 := by
  have him := abs_im_le_norm w
  have hre := abs_re_le_norm w
  have hA : 0 < 1 - w.im := by linarith [(abs_le.mp (him.trans hw)).2]
  have hB : |-w.re| < 1 / 2 * (1 - w.im) := by
    rw [abs_neg]
    have := (abs_le.mp (him.trans hw)).2
    linarith [hre.trans hw]
  rw [one_add_I_mul_eq_sub_mul_I]
  exact abs_arg_sub_mul_I_lt hA hB

/-- Norm of one cpow factor: `‖z^c‖ ≤ (3/4)^{-1/4} e^{|s|/4}` when `‖z‖ ≥ 3/4`, `|arg z| < 1/2`,
`c.re = -1/4`, `|c.im| = |s|/2`. -/
theorem norm_cpow_factor_le {z c : ℂ} {s : ℝ} (hz : 3 / 4 ≤ ‖z‖) (harg : |z.arg| < 1 / 2)
    (hre : c.re = -(1 / 4)) (him : |c.im| = |s| / 2) :
    ‖z ^ c‖ ≤ (3 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (|s| / 4) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  rw [norm_cpow_of_ne_zero hz0, hre]
  have h1 : ‖z‖ ^ (-(1 / 4 : ℝ)) ≤ (3 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hz (by norm_num))
  have h2 : 1 / Real.exp (z.arg * c.im) ≤ Real.exp (|s| / 4) := by
    rw [one_div, ← Real.exp_neg, Real.exp_le_exp]
    have : |z.arg * c.im| ≤ |s| / 4 := by
      rw [abs_mul, him]
      have := mul_le_mul_of_nonneg_right harg.le (by positivity : (0 : ℝ) ≤ |s| / 2)
      linarith
    linarith [(abs_le.mp this).1]
  calc ‖z‖ ^ (-(1 / 4 : ℝ)) / Real.exp (z.arg * c.im)
      = ‖z‖ ^ (-(1 / 4 : ℝ)) * (1 / Real.exp (z.arg * c.im)) := by ring
    _ ≤ (3 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (|s| / 4) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Sphere bound for the generating function:** `‖G_s(w)‖ ≤ (3/4)^{-1/2} e^{|s|/2}` for
`‖w‖ ≤ 1/4`. -/
theorem norm_mpGeneratingFunction_le (s : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    ‖mpGeneratingFunction s w‖ ≤ (3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) := by
  unfold mpGeneratingFunction
  rw [norm_mul]
  have hA := norm_cpow_factor_le (s := s) (three_quarters_le_norm_one_sub_I_mul hw)
    (abs_arg_one_sub_I_mul_lt hw) (mpExponentPlus_re s)
    (by rw [mpExponentPlus_im, abs_div]; norm_num)
  have hB := norm_cpow_factor_le (s := s) (three_quarters_le_norm_one_add_I_mul hw)
    (abs_arg_one_add_I_mul_lt hw) (mpExponentMinus_re s)
    (by rw [mpExponentMinus_im, abs_neg, abs_div]; norm_num)
  calc ‖(1 - I * w) ^ mpExponentPlus s‖ * ‖(1 + I * w) ^ mpExponentMinus s‖
      ≤ ((3 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (|s| / 4)) *
          ((3 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (|s| / 4)) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ = (3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) := by
        rw [show (-(1 / 2 : ℝ)) = (-(1 / 4 : ℝ)) + (-(1 / 4 : ℝ)) by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 4),
          show |s| / 2 = |s| / 4 + |s| / 4 by ring, Real.exp_add]
        ring

/-- **Cauchy bound for the coefficients:** `|c_m p_m(s)| ≤ (3/4)^{-1/2} e^{|s|/2} 4^m`. -/
theorem abs_mpCoefficient_le (s : ℝ) (m : ℕ) :
    |mpCoefficient s m| ≤ (3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) * 4 ^ m := by
  have hdiff : DiffContOnCl ℂ (mpGeneratingFunction s) (Metric.ball (0 : ℂ) (1 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    exact (differentiableOn_mpGeneratingFunction s).mono
      (Metric.closedBall_subset_ball (by norm_num))
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 4),
      ‖mpGeneratingFunction s z‖ ≤ (3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact norm_mpGeneratingFunction_le s hz.le
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num) hdiff hbound
  have hD : iteratedDeriv m (mpGeneratingFunction s) 0 =
      (m.factorial : ℂ) * (mpCoefficient s m : ℂ) :=
    mpDerivative_eq_factorial_mul_coefficient s m
  rw [hD, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at h
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h4 : ((1 / 4 : ℝ)) ^ m = 1 / 4 ^ m := by rw [one_div_pow]
  rw [h4, div_div_eq_mul_div, div_one] at h
  have h' : (m.factorial : ℝ) * |mpCoefficient s m| ≤
      (m.factorial : ℝ) * ((3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) * 4 ^ m) := by
    calc (m.factorial : ℝ) * |mpCoefficient s m| ≤ _ := h
      _ = (m.factorial : ℝ) * ((3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (|s| / 2) * 4 ^ m) := by
          ring
  exact le_of_mul_le_mul_left h' hf

end MeixnerPollaczek

end RHTower
