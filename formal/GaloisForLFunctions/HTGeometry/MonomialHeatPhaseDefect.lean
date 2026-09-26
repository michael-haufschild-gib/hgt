import GaloisForLFunctions.HTGeometry.QuadraticHeatPhaseDefect

/-!
# Imaginary displacement bounds for every monomial heat channel

A monomial's imaginary part costs one imaginary displacement and at most its
degree times the remaining norm power. Combined with the half-heat phase this
gives the two Gaussian norm moments needed to control arbitrary polynomial
degrees, without assuming the spectral coordinate is real.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem abs_im_pow_succ_le (z : ℂ) (n : ℕ) :
    |(z ^ (n + 1)).im| ≤ (n + 1 : ℝ) * |z.im| * ‖z‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ z (n + 1), Complex.mul_im]
    calc
      |(z ^ (n + 1)).re * z.im + (z ^ (n + 1)).im * z.re| ≤
          |(z ^ (n + 1)).re| * |z.im| + |(z ^ (n + 1)).im| * |z.re| := by
        simpa only [abs_mul] using abs_add_le
          ((z ^ (n + 1)).re * z.im) ((z ^ (n + 1)).im * z.re)
      _ ≤ ‖z ^ (n + 1)‖ * |z.im| +
          ((n + 1 : ℝ) * |z.im| * ‖z‖ ^ n) * ‖z‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (abs_nonneg _)
        · exact mul_le_mul ih (Complex.abs_re_le_norm z) (abs_nonneg _)
            (by positivity)
      _ = _ := by
        rw [norm_pow, pow_succ]
        push_cast
        ring

theorem im_pow_succ_sq_le (z : ℂ) (n : ℕ) :
    (z ^ (n + 1)).im ^ 2 ≤ (n + 1 : ℝ) ^ 2 * z.im ^ 2 * ‖z‖ ^ (2 * n) := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (abs_im_pow_succ_le z n)
  simpa only [mul_pow, sq_abs, ← pow_mul, Nat.mul_comm n 2] using h

/-- The complete monomial heat phase debt, including its mixed phase contribution. -/
theorem monomialHeatPhaseDebt_bound (n : ℕ) (t : ℝ) (z : ℂ) :
    2 * (heatPhaseAmplitude (z ^ (n + 1)) t z).im ^ 2 ≤
      Real.exp (-(t * z.re)) * z.im ^ 2 *
        (4 * (n + 1 : ℝ) ^ 2 * ‖z‖ ^ (2 * n) + t ^ 2 * ‖z‖ ^ (2 * (n + 1))) := by
  have hi := im_pow_succ_sq_le z n
  have hr : (z ^ (n + 1)).re ^ 2 ≤ ‖z‖ ^ (2 * (n + 1)) := by
    have h := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
      (Complex.abs_re_le_norm (z ^ (n + 1)))
    simpa only [sq_abs, norm_pow, ← pow_mul, Nat.mul_comm (n + 1) 2] using h
  have hbase := heatPhaseAmplitude_im_sq_bound (z ^ (n + 1)) t z
  have hmul := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ t ^ 2 * z.im ^ 2 / 2 by positivity)
  have hpoly : 2 * (z ^ (n + 1)).im ^ 2 +
      t ^ 2 * z.im ^ 2 / 2 * (z ^ (n + 1)).re ^ 2 ≤
      2 * ((n + 1 : ℝ) ^ 2 * z.im ^ 2 * ‖z‖ ^ (2 * n)) +
        t ^ 2 * z.im ^ 2 / 2 * ‖z‖ ^ (2 * (n + 1)) := by
    linarith
  have h := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
  nlinarith only [hbase, h]

end
end GaloisForLFunctions.HTGeometry
