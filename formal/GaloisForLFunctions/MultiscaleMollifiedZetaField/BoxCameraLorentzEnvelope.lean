import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraProfileMass

/-!
# An order-independent Lorentzian envelope for box cameras

Keep one box for quadratic Fourier decay and bound the other boxes by
their unit mass. Combined with the exact camera mass, this controls every
frequency, including zero. Positive imaginary parts then supply the
exponential damping needed for shallow zeros.
-/

noncomputable section

open Complex MeasureTheory Set
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

theorem norm_paperFT_boxPlateau_le_reserved {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      (2 / h) / ‖z‖ ^ 2 * Real.exp (boxCameraRadius A h n r * |z.im|) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : Real.exp (A * |z.im|) * Real.exp (h * |z.im|) *
      Real.exp ((n : ℝ) * (h * |z.im|)) * Real.exp (r * |z.im|) =
      Real.exp (boxCameraRadius A h n r * |z.im|) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [boxCameraRadius, Nat.cast_add, Nat.cast_one]
    ring
  rw [paperFT_boxPlateau hh hr, norm_mul, norm_mul, norm_pow]
  calc
    _ = (‖paperFT (boxPower A h 0) z‖ * ‖paperFT (unitBox h) z‖) *
        ‖paperFT (unitBox h) z‖ ^ n * ‖paperFT (smoothUnitBump r) z‖ := by
      rw [pow_succ]
      ring
    _ ≤ (2 * Real.exp (A * |z.im|) / ‖z‖ *
        (Real.exp (h * |z.im|) / (h * ‖z‖))) *
        Real.exp (h * |z.im|) ^ n * Real.exp (r * |z.im|) := by
      gcongr
      · exact norm_paperFT_boxPower_zero_le hA hz
      · exact norm_paperFT_unitBox_le hh hz
      · exact norm_paperFT_unitBox_le_mass hh z
      · exact norm_paperFT_smoothUnitBump_le hr z
    _ = (2 / h) / ‖z‖ ^ 2 *
        (Real.exp (A * |z.im|) * Real.exp (h * |z.im|) *
          Real.exp ((n : ℝ) * (h * |z.im|)) * Real.exp (r * |z.im|)) := by
      rw [← Real.exp_nat_mul]
      field_simp [hh.ne', hn.ne']
    _ = _ := by rw [he]

/-- The constant is independent of convolution order. -/
theorem norm_paperFT_boxPlateau_le_lorentz {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) (z : ℂ) :
    ‖paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      (4 * A + 4 / h) * Real.exp (boxCameraRadius A h n r * |z.im|) *
        (1 / (1 + z.re ^ 2)) := by
  have hden : 0 < 1 + z.re ^ 2 := by positivity
  have hE : 0 < Real.exp (boxCameraRadius A h n r * |z.im|) := Real.exp_pos _
  by_cases hx : |z.re| ≤ 1
  · have hx2 : z.re ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hx 2
    refine (norm_paperFT_boxPlateau_le_mass hA hh hr n z).trans ?_
    rw [mul_one_div, le_div_iff₀ hden]
    calc
      _ ≤ (2 * A * Real.exp (boxCameraRadius A h n r * |z.im|)) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [hx2]) (by positivity)
      _ ≤ _ := by
        have hp := mul_nonneg (by positivity : 0 ≤ 4 / h) hE.le
        nlinarith only [hp]
  · have hx1 : 1 < |z.re| := lt_of_not_ge hx
    have hn : 0 < ‖z‖ := (zero_lt_one.trans hx1).trans_le (Complex.abs_re_le_norm z)
    have hx2 : 1 ≤ z.re ^ 2 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ zero_le_one hx1.le 2
    have hn2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
    have hi : 1 / ‖z‖ ^ 2 ≤ 2 / (1 + z.re ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) hden, one_mul]
      linarith only [hx2, hn2]
    refine (norm_paperFT_boxPlateau_le_reserved hA hh hr n (norm_pos_iff.mp hn)).trans ?_
    calc
      _ = ((2 / h) * Real.exp (boxCameraRadius A h n r * |z.im|)) * (1 / ‖z‖ ^ 2) := by ring
      _ ≤ ((2 / h) * Real.exp (boxCameraRadius A h n r * |z.im|)) *
          (2 / (1 + z.re ^ 2)) := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (4 / h) * Real.exp (boxCameraRadius A h n r * |z.im|) *
          (1 / (1 + z.re ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hE.le)
        (by positivity)

/-- A positive imaginary part gives damping by distance from the support. -/
theorem norm_damped_boxPlateau_le_lorentz {A h r y d : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    (hy : boxCameraRadius A h n r ≤ y) (hd : 0 ≤ d) {z : ℂ} (hzi : d ≤ z.im) :
    ‖Complex.exp (I * z * y) * paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r))) *
        (1 / (1 + z.re ^ 2)) := by
  have hz0 := hd.trans hzi
  have he : Real.exp (-(z.im * y)) * Real.exp (boxCameraRadius A h n r * |z.im|) =
      Real.exp (-(z.im * (y - boxCameraRadius A h n r))) := by
    rw [abs_of_nonneg hz0, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-(z.im * (y - boxCameraRadius A h n r))) ≤
      Real.exp (-(d * (y - boxCameraRadius A h n r))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hzi (sub_nonneg.mpr hy))
  rw [norm_mul, Complex.norm_exp, show (I * z * (y : ℂ)).re = -(z.im * y) by simp]
  calc
    _ ≤ Real.exp (-(z.im * y)) *
        ((4 * A + 4 / h) * Real.exp (boxCameraRadius A h n r * |z.im|) *
          (1 / (1 + z.re ^ 2))) :=
      mul_le_mul_of_nonneg_left (norm_paperFT_boxPlateau_le_lorentz hA hh hr n z)
        (Real.exp_pos _).le
    _ = (4 * A + 4 / h) * Real.exp (-(z.im * (y - boxCameraRadius A h n r))) *
        (1 / (1 + z.re ^ 2)) := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity))
      (by positivity)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
