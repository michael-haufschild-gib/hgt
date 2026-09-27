import GaloisForLFunctions.HTGeometry.QuadraticHeatPhaseDefect

/-!
# Transverse bounds for polynomial heat amplitudes

The imaginary amplitude is charged to the imaginary part of its spectral
coordinate before any square or coefficient estimate is taken. Thus every
bound vanishes exactly on the real axis and retains the full heat phase.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem abs_im_pow_mul_norm_le (z : ℂ) (j : ℕ) :
    |(z ^ j).im| * ‖z‖ ≤ (j : ℝ) * |z.im| * ‖z‖ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp : |(z ^ (j + 1)).im| ≤
        ‖z‖ ^ j * |z.im| + |(z ^ j).im| * ‖z‖ := by
      rw [pow_succ, Complex.mul_im]
      calc
        _ ≤ |(z ^ j).re * z.im| + |(z ^ j).im * z.re| := abs_add_le _ _
        _ ≤ ‖z‖ ^ j * |z.im| + |(z ^ j).im| * ‖z‖ := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (by simpa only [norm_pow] using Complex.abs_re_le_norm (z ^ j))
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _))
    have h := mul_le_mul_of_nonneg_right hp (norm_nonneg z)
    have hi := mul_le_mul_of_nonneg_right ih (norm_nonneg z)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ ‖z‖ j]
    nlinarith only [h, hi]

theorem abs_im_exp_neg_mul_le (z : ℂ) (h : {h : ℝ // 0 ≤ h}) :
    |(Complex.exp (-((h : ℝ) : ℂ) * z)).im| ≤
      Real.exp (-((h : ℝ) * z.re)) * (h : ℝ) * |z.im| := by
  rw [Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs := mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_abs (x := (-((h : ℝ) : ℂ) * z).im))
    (Real.exp_pos ((-((h : ℝ) : ℂ) * z).re)).le
  simpa only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero,
    add_zero, neg_mul, abs_neg, abs_mul, abs_of_nonneg h.property, mul_assoc] using hs

/-- All monomial and heat-phase contributions remain in the transverse estimate. -/
theorem abs_im_pow_heat_mul_norm_le (z : ℂ) (j : ℕ) (h : {h : ℝ // 0 ≤ h}) :
    |(z ^ j * Complex.exp (-((h : ℝ) : ℂ) * z)).im| * ‖z‖ ≤
      Real.exp (-((h : ℝ) * z.re)) * |z.im| * ‖z‖ ^ j *
        ((j : ℝ) + (h : ℝ) * ‖z‖) := by
  let w := Complex.exp (-((h : ℝ) : ℂ) * z)
  let E := Real.exp (-((h : ℝ) * z.re))
  have hw : ‖w‖ = E := by
    rw [Complex.norm_exp]
    simp only [E, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, neg_mul]
  have hwi : |w.im| ≤ E * (h : ℝ) * |z.im| := abs_im_exp_neg_mul_le z h
  have hp : |(z ^ j * w).im| ≤
      ‖z‖ ^ j * (E * (h : ℝ) * |z.im|) + |(z ^ j).im| * E := by
    rw [Complex.mul_im]
    calc
      _ ≤ |(z ^ j).re * w.im| + |(z ^ j).im * w.re| := abs_add_le _ _
      _ ≤ ‖z‖ ^ j * (E * (h : ℝ) * |z.im|) + |(z ^ j).im| * E := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul (by simpa only [norm_pow] using Complex.abs_re_le_norm (z ^ j))
            hwi (abs_nonneg _) (pow_nonneg (norm_nonneg z) _))
          (mul_le_mul_of_nonneg_left (by simpa only [hw] using Complex.abs_re_le_norm w)
            (abs_nonneg _))
  have hpw := mul_le_mul_of_nonneg_right hp (norm_nonneg z)
  have hpow := mul_le_mul_of_nonneg_right (abs_im_pow_mul_norm_le z j)
    (show 0 ≤ E from (Real.exp_pos _).le)
  change |(z ^ j * w).im| * ‖z‖ ≤ E * |z.im| * ‖z‖ ^ j * _
  nlinarith only [hpw, hpow]

/-- A monomial's complete heat phase is controlled by reciprocal transverse orientation.
The two terms account for polynomial phase and heat phase separately. -/
theorem pow_heat_im_sq_le_reciprocal_orientation
    (z : {z : ℂ // z ≠ 0}) (j : ℕ) (t : ℝ) :
    (heatPhaseAmplitude ((z : ℂ) ^ j) t z).im ^ 2 ≤
      (((z : ℂ)⁻¹).im ^ 2) *
        (2 * (j : ℝ) ^ 2 * ‖(z : ℂ)‖ ^ (2 * j + 2) +
          (t ^ 2 / 2) * ‖(z : ℂ)‖ ^ (2 * j + 4)) *
            Real.exp (-(t * (z : ℂ).re)) := by
  let r := ‖(z : ℂ)‖
  let E := Real.exp (-(t * (z : ℂ).re))
  have hr : 0 < r := norm_pos_iff.mpr z.property
  have hp := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hr.le)
    (abs_im_pow_mul_norm_le z j) 2
  simp only [mul_pow, sq_abs, ← pow_mul, Nat.mul_comm j 2] at hp
  have hre := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm ((z : ℂ) ^ j)) 2
  simp only [sq_abs, norm_pow, ← pow_mul, Nat.mul_comm j 2] at hre
  have hi := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2)
  have hreal := mul_le_mul_of_nonneg_right hre
    (show 0 ≤ t ^ 2 * (z : ℂ).im ^ 2 / 2 * r ^ 2 by positivity)
  have hinner :
      (2 * ((z : ℂ) ^ j).im ^ 2 + t ^ 2 * (z : ℂ).im ^ 2 / 2 * ((z : ℂ) ^ j).re ^ 2) * r ^ 2 ≤
        (z : ℂ).im ^ 2 * (2 * (j : ℝ) ^ 2 * r ^ (2 * j) +
          t ^ 2 / 2 * r ^ (2 * j + 2)) := by
    dsimp only [r] at *
    rw [pow_add]
    nlinarith only [hi, hreal]
  have himid : (((z : ℂ)⁻¹).im ^ 2) * r ^ 4 = (z : ℂ).im ^ 2 := by
    rw [Complex.inv_im, ← Complex.sq_norm]
    dsimp only [r]
    field_simp [(norm_pos_iff.mpr z.property).ne']
  apply (mul_le_mul_iff_of_pos_right (pow_pos hr 2)).mp
  calc
    _ ≤ (E * (2 * ((z : ℂ) ^ j).im ^ 2 +
        t ^ 2 * (z : ℂ).im ^ 2 / 2 * ((z : ℂ) ^ j).re ^ 2)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right (heatPhaseAmplitude_im_sq_bound ((z : ℂ) ^ j) t z)
        (sq_nonneg r)
    _ = E * ((2 * ((z : ℂ) ^ j).im ^ 2 +
        t ^ 2 * (z : ℂ).im ^ 2 / 2 * ((z : ℂ) ^ j).re ^ 2) * r ^ 2) := by ring
    _ ≤ E * ((z : ℂ).im ^ 2 * (2 * (j : ℝ) ^ 2 * r ^ (2 * j) +
        t ^ 2 / 2 * r ^ (2 * j + 2))) := mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
    _ = _ := by
      rw [← himid]
      change E * _ = (((z : ℂ)⁻¹).im ^ 2) *
        (2 * (j : ℝ) ^ 2 * r ^ (2 * j + 2) + (t ^ 2 / 2) * r ^ (2 * j + 4)) * E * r ^ 2
      simp only [pow_add]
      ring

end GaloisForLFunctions.HTGeometry
