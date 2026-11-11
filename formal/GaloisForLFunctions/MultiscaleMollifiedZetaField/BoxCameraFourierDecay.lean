import GaloisForLFunctions.RHTower.BoxConvolutionPlateau
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound

/-!
# Exponential exterior decay from box convolutions

One box factor and the initial interval supply a square-integrable frequency
denominator. Every further box supplies another factor `1/(h g)` outside
an ordinate gap `g`. The profile varies with its convolution order; no
exponential decay is asserted for a fixed compact profile.
-/

noncomputable section

open Complex MeasureTheory Set
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The support radius of an interval convolved with `n+1` boxes and a smooth bump. -/
def boxCameraRadius (A h : ℝ) (n : ℕ) (r : ℝ) : ℝ := A + (n + 1) * h + r

/-- A translated box-convolution camera, exponentially centered at depth `b`. -/
def boxCenteredCamera (A h : ℝ) (n : ℕ) (r b y : ℝ) : ℝ → ℂ :=
  fun u => boxPlateau A h (n + 1) r (u - y) * Complex.exp (-(b : ℂ) * u)

theorem paperFT_boxCenteredCamera (A h : ℝ) (n : ℕ) (r b y : ℝ) (z : ℂ) :
    paperFT (boxCenteredCamera A h n r b y) z =
      Complex.exp (I * (z + I * b) * y) * paperFT (boxPlateau A h (n + 1) r) (z + I * b) := by
  have he : paperFT (boxCenteredCamera A h n r b y) z =
      paperFT (fun u => boxPlateau A h (n + 1) r (u - y)) (z + I * b) := by
    unfold boxCenteredCamera paperFT
    congr 1
    funext u
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    linear_combination -(b : ℂ) * (u : ℂ) * Complex.I_sq
  rw [he, RHTower.paperFT_translate']

theorem contDiff_boxCenteredCamera {A h r b y : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ 2 (boxCenteredCamera A h n r b y) := by
  unfold boxCenteredCamera
  exact ((contDiff_boxPlateau (A := A) (h := h) hr (n + 1)).comp
    (contDiff_id.sub contDiff_const)).mul (by fun_prop)

theorem boxCenteredCamera_support {A h r b y u : ℝ} (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hu : boxCenteredCamera A h n r b y u ≠ 0) :
    |u - y| ≤ boxCameraRadius A h n r := by
  by_contra hn
  apply hu
  rw [boxCenteredCamera, boxPlateau_eq_zero hh hr (n + 1) (le_of_not_ge hn), zero_mul]

/-- The complete Fourier estimate retains the damping from positive lags. -/
theorem norm_damped_boxPlateau_le {A h r y : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    {z : ℂ} (hz : z ≠ 0) (hzi : 0 ≤ z.im) :
    ‖Complex.exp (I * z * y) * paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      (2 / h) * (1 / (h * ‖z‖)) ^ n / ‖z‖ ^ 2 *
        Real.exp (-((y - boxCameraRadius A h n r) * z.im)) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hexp :
      Real.exp (-(z.im * y)) * Real.exp (A * z.im) *
        Real.exp (((n + 1 : ℕ) : ℝ) * (h * z.im)) * Real.exp (r * z.im) =
      Real.exp (-((y - boxCameraRadius A h n r) * z.im)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [boxCameraRadius, Nat.cast_add, Nat.cast_one]
    ring
  rw [norm_mul, Complex.norm_exp, show (I * z * (y : ℂ)).re = -(z.im * y) by simp]
  calc
    _ ≤ Real.exp (-(z.im * y)) *
        (2 * Real.exp (A * |z.im|) / ‖z‖ *
          (Real.exp (h * |z.im|) / (h * ‖z‖)) ^ (n + 1) * Real.exp (r * |z.im|)) :=
      mul_le_mul_of_nonneg_left (norm_paperFT_boxPlateau_le hA hh hr (n + 1) hz)
        (Real.exp_pos _).le
    _ = (2 / h) * (1 / (h * ‖z‖)) ^ n / ‖z‖ ^ 2 *
        (Real.exp (-(z.im * y)) * Real.exp (A * z.im) *
          Real.exp (((n + 1 : ℕ) : ℝ) * (h * z.im)) * Real.exp (r * z.im)) := by
      rw [abs_of_nonneg hzi]
      simp only [div_pow, one_pow]
      rw [← Real.exp_nat_mul, pow_succ]
      field_simp [hh.ne', hz0.ne']
      ring
    _ = _ := by rw [hexp]

/-- A separated frequency pays the unit Lorentzian envelope. -/
private theorem inv_norm_sq_le_unit_of_gap {z : ℂ} {g : ℝ}
    (hg : 0 < g) (hgap : g ≤ |z.re|) :
    1 / ‖z‖ ^ 2 ≤ ((1 + g ^ 2) / g ^ 2) * (1 / (1 + z.re ^ 2)) := by
  have hgn := hgap.trans (Complex.abs_re_le_norm z)
  have hn : 0 < ‖z‖ := hg.trans_le hgn
  have hg2 := pow_le_pow_left₀ hg.le hgn 2
  have hx2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) (Complex.abs_re_le_norm z) 2
  have hp := mul_nonneg (sq_nonneg g) (sub_nonneg.mpr hx2)
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith only [hg2, hp]

/-- Outside a fixed ordinate gap, every additional box gives geometric decay,
while one reserved box retains the summable Lorentzian denominator. -/
theorem norm_damped_boxPlateau_le_of_gap {A h r y g : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (hg : 0 < g) (n : ℕ)
    (hy : boxCameraRadius A h n r ≤ y) {z : ℂ}
    (hzi : 0 ≤ z.im) (hgap : g ≤ |z.re|) :
    ‖Complex.exp (I * z * y) * paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) *
        (1 / (1 + z.re ^ 2)) := by
  have hgn := hgap.trans (Complex.abs_re_le_norm z)
  have hn : 0 < ‖z‖ := hg.trans_le hgn
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (h * ‖z‖))
    (one_div_le_one_div_of_le (mul_pos hh hg) (mul_le_mul_of_nonneg_left hgn hh.le)) n
  have he : Real.exp (-((y - boxCameraRadius A h n r) * z.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hy) hzi))
  calc
    _ ≤ (2 / h) * (1 / (h * ‖z‖)) ^ n / ‖z‖ ^ 2 *
        Real.exp (-((y - boxCameraRadius A h n r) * z.im)) :=
      norm_damped_boxPlateau_le hA hh hr n (norm_pos_iff.mp hn) hzi
    _ ≤ (2 / h) * (1 / (h * ‖z‖)) ^ n / ‖z‖ ^ 2 :=
      mul_le_of_le_one_right (by positivity) he
    _ = (2 / h) * (1 / (h * ‖z‖)) ^ n * (1 / ‖z‖ ^ 2) := by ring
    _ ≤ (2 / h) * (1 / (h * g)) ^ n *
        (((1 + g ^ 2) / g ^ 2) * (1 / (1 + z.re ^ 2))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (inv_norm_sq_le_unit_of_gap hg hgap) (by positivity) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
