import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheBoxCameraSeesNearTopClusters
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCenteredCameraRemainder

/-!
# Uniform explicit-formula costs for box cameras

The unit-scale Lorentzian envelope bounds the gamma integral uniformly
in convolution order. The same envelope controls the pole terms when the
camera support ends below `log t`. These bounds use the actual camera,
without profile-dependent derivative constants.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

def boxCameraPoly (A h : ℝ) (n : ℕ) (r b y t : ℝ) : ℂ :=
  depthCenteredCameraPoly (boxTuranProfile A h n r) b (boxCameraRadius A h n r) y t

theorem norm_paperFT_boxCenteredCamera_real_le
    {A h r b y : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    (hb : 0 ≤ b) (hy : boxCameraRadius A h n r ≤ y) (x : ℝ) :
    ‖paperFT (boxCenteredCamera A h n r b y) x‖ ≤
      (4 * A + 4 / h) * Real.exp (-(b * (y - boxCameraRadius A h n r))) *
        (1 + x ^ 2)⁻¹ := by
  rw [paperFT_boxCenteredCamera]
  have hz : ((x : ℂ) + I * b).im = b := by simp
  have hf := norm_damped_boxPlateau_le_lorentz hA hh hr n hy hb
    (z := (x : ℂ) + I * (b : ℂ)) (le_of_eq hz.symm)
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, one_div] using hf

theorem exists_norm_gamma_boxCenteredCamera_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A h r b y t : ℝ, ∀ n : ℕ,
      0 ≤ A → 0 < h → 0 < r → 0 ≤ b → boxCameraRadius A h n r ≤ y →
      ‖∫ x : ℝ, paperFT (boxCenteredCamera A h n r b y) x * (mu (x + t) : ℂ)‖ ≤
        C * (4 * A + 4 / h) * Real.exp (-(b * (y - boxCameraRadius A h n r))) *
          (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_gamma_lorentz_le
  refine ⟨C, hC0, fun A h r b y t n hA hh hr hb hy => ?_⟩
  have hf := hC 1 t ((4 * A + 4 / h) *
    Real.exp (-(b * (y - boxCameraRadius A h n r))))
    (fun x => paperFT (boxCenteredCamera A h n r b y) x) le_rfl (by positivity)
    (fun x => by simpa only [one_mul] using
      norm_paperFT_boxCenteredCamera_real_le hA hh hr n hb hy x)
  simpa only [div_one, mul_assoc] using hf

theorem norm_paperFT_boxCenteredCamera_pole_le
    {A h r b y t q : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    (hb : 0 ≤ b) (hy : boxCameraRadius A h n r ≤ y) (ht : 1 ≤ t)
    (hT : Real.exp (y + boxCameraRadius A h n r) ≤ t) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖paperFT (boxCenteredCamera A h n r b y) (gammaOf (q : ℂ) - t)‖ ≤
      (4 * A + 4 / h) * Real.exp (-(b * (y - boxCameraRadius A h n r))) := by
  let z := gammaOf (q : ℂ) - (t : ℂ) + I * (b : ℂ)
  have hzr : z.re = -t := by simp [z, ZeroConfigurationGeometry.gammaOf_eq]
  have hzi : z.im = b + 1 / 2 - q := by
    simp [z, ZeroConfigurationGeometry.gammaOf_eq, ZeroConfigurationGeometry.depth] <;> ring
  have hδ := (boxCameraRadius_pos hA hh hr n).le
  have hy0 := hδ.trans hy
  have hab : |z.im| ≤ b + 1 / 2 := by
    rw [hzi, abs_le]
    constructor <;> linarith only [hq0, hq1, hb]
  have he : -(z.im * y) + boxCameraRadius A h n r * |z.im| ≤
      -(b * (y - boxCameraRadius A h n r)) + (y + boxCameraRadius A h n r) := by
    have h1 := mul_le_mul_of_nonneg_left hab hδ
    have h2 := mul_le_mul_of_nonneg_right hq1 hy0
    rw [hzi] at h1 ⊢
    nlinarith only [h1, h2, hy0, hδ]
  have hE : Real.exp (-(z.im * y)) * Real.exp (boxCameraRadius A h n r * |z.im|) ≤
      Real.exp (-(b * (y - boxCameraRadius A h n r))) * (1 + t ^ 2) := by
    rw [← Real.exp_add]
    calc
      _ ≤ Real.exp (-(b * (y - boxCameraRadius A h n r)) +
          (y + boxCameraRadius A h n r)) := Real.exp_le_exp.mpr he
      _ = Real.exp (-(b * (y - boxCameraRadius A h n r))) *
          Real.exp (y + boxCameraRadius A h n r) := Real.exp_add _ _
      _ ≤ Real.exp (-(b * (y - boxCameraRadius A h n r))) * t :=
        mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [ht]) (Real.exp_pos _).le
  rw [paperFT_boxCenteredCamera]
  change ‖Complex.exp (I * z * y) * paperFT (boxPlateau A h (n + 1) r) z‖ ≤ _
  rw [norm_mul, Complex.norm_exp, show (I * z * (y : ℂ)).re = -(z.im * y) by simp]
  have hf := mul_le_mul_of_nonneg_left (norm_paperFT_boxPlateau_le_lorentz hA hh hr n z)
    (Real.exp_pos (-(z.im * y))).le
  rw [hzr, neg_sq] at hf
  apply hf.trans
  calc
    _ = ((4 * A + 4 / h) *
        (Real.exp (-(z.im * y)) * Real.exp (boxCameraRadius A h n r * |z.im|))) *
        (1 / (1 + t ^ 2)) := by ring
    _ ≤ ((4 * A + 4 / h) *
        (Real.exp (-(b * (y - boxCameraRadius A h n r))) * (1 + t ^ 2))) *
        (1 / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
    _ = _ := by
      have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp [hden]

theorem widthCenteredBoxZeroField_add_poly_eq
    {A h r y : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ)
    (hy : boxCameraRadius A h n r < y) (t : ℝ) :
    widthCenteredBoxZeroField A h n r y t + boxCameraPoly A h n r zetaZeroWidth y t =
      paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (I / 2 - t) +
      paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (-I / 2 - t) +
      ∫ x : ℝ, paperFT (boxCenteredCamera A h n r zetaZeroWidth y) x * (mu (x + t) : ℂ) := by
  have he := widthCenteredZeroField_add_poly_eq (contDiff_boxTuranProfile hr n)
    (boxTuranProfile_support hA hh hr n) (boxCameraRadius_pos hA hh hr n) hy t
  simpa only [widthCenteredZeroField, widthCenteredBoxZeroField, boxCameraPoly,
    depthCenteredCamera_boxTuranProfile hA hh hr n] using he

/-- One constant covers every convolution order, width, and camera centre. -/
theorem exists_norm_widthCenteredBoxZeroField_add_poly_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A h r y t : ℝ, ∀ n : ℕ,
      0 ≤ A → 0 < h → 0 < r → boxCameraRadius A h n r < y → 1 ≤ t →
      Real.exp (y + boxCameraRadius A h n r) ≤ t →
      ‖widthCenteredBoxZeroField A h n r y t + boxCameraPoly A h n r zetaZeroWidth y t‖ ≤
        C * (4 * A + 4 / h) * Real.exp (-(zetaZeroWidth * (y - boxCameraRadius A h n r))) *
          (1 + Real.log (2 + t)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_gamma_boxCenteredCamera_le
  refine ⟨C + 2, by positivity, fun A h r y t n hA hh hr hy ht hT => ?_⟩
  have hb := SquareRootThreshold.zetaZeroWidth_nonneg
  have h0 := norm_paperFT_boxCenteredCamera_pole_le hA hh hr n hb hy.le ht hT
    (q := 0) (by norm_num) (by norm_num)
  have h1 := norm_paperFT_boxCenteredCamera_pole_le hA hh hr n hb hy.le ht hT
    (q := 1) (by norm_num) (by norm_num)
  have he0 : gammaOf (0 : ℂ) = I / 2 := by simp only [gammaOf, Complex.div_I]; ring
  have he1 : gammaOf (1 : ℂ) = -I / 2 := by simp only [gammaOf, Complex.div_I]; ring
  rw [Complex.ofReal_zero, he0] at h0
  rw [Complex.ofReal_one, he1] at h1
  have hG := hC A h r zetaZeroWidth y t n hA hh hr hb hy.le
  rw [abs_of_nonneg (zero_le_one.trans ht)] at hG
  rw [widthCenteredBoxZeroField_add_poly_eq hA hh hr n hy t]
  have htri := (norm_add_le
    (paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (I / 2 - t) +
      paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (-I / 2 - t))
    (∫ x : ℝ, paperFT (boxCenteredCamera A h n r zetaZeroWidth y) x * (mu (x + t) : ℂ))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hgain : 0 ≤ (4 * A + 4 / h) *
      Real.exp (-(zetaZeroWidth * (y - boxCameraRadius A h n r))) := by positivity
  have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith only [ht])
  nlinarith only [htri, h0, h1, hG, mul_nonneg hgain hlog]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
