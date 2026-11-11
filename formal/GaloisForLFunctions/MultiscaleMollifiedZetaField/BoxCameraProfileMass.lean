import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraFourierDecay

/-!
# Positive box cameras and their exact mass

Convolution with a positive unit-mass kernel preserves positivity and total
mass. Thus the box camera has mass `2A` at every convolution order, even
when its support radius grows. Compact support converts this mass into a
Fourier bound valid also at zero frequency.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem positiveReal_integral {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ (f u).re ∧ ((f u).re : ℂ) = f u) :
    0 ≤ (∫ u, f u).re ∧ (((∫ u, f u).re : ℝ) : ℂ) = ∫ u, f u := by
  have he : f = fun u => ((f u).re : ℂ) := funext fun u => (hf u).2.symm
  rw [he, integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  exact ⟨integral_nonneg fun u => (hf u).1, True.intro⟩

private theorem positiveReal_mul {a b : ℂ}
    (ha : 0 ≤ a.re ∧ (a.re : ℂ) = a)
    (hb : 0 ≤ b.re ∧ (b.re : ℂ) = b) :
    0 ≤ (a * b).re ∧ ((a * b).re : ℂ) = a * b := by
  rw [← ha.2, ← hb.2, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact ⟨mul_nonneg ha.1 hb.1, rfl⟩

theorem positiveReal_unitBox {h : ℝ} (hh : 0 < h) (u : ℝ) :
    0 ≤ (unitBox h u).re ∧ ((unitBox h u).re : ℂ) = unitBox h u := by
  unfold unitBox
  by_cases hu : u ∈ Icc (-h) h
  · rw [indicator_of_mem hu, Complex.ofReal_re]
    exact ⟨by positivity, rfl⟩
  · simp only [indicator_of_notMem hu, Complex.zero_re, Complex.ofReal_zero, le_refl,
      and_self]

theorem positiveReal_boxPower {A h : ℝ} (hh : 0 < h) : ∀ n u,
    0 ≤ (boxPower A h n u).re ∧ ((boxPower A h n u).re : ℂ) = boxPower A h n u
  | 0, u => by
    rw [boxPower_zero]
    by_cases hu : u ∈ Icc (-A) A
    · simp only [indicator_of_mem hu, Complex.one_re, Complex.ofReal_one, zero_le_one,
        and_self]
    · simp only [indicator_of_notMem hu, Complex.zero_re, Complex.ofReal_zero, le_refl,
        and_self]
  | n + 1, u => by
    rw [boxPower_succ_apply]
    exact positiveReal_integral fun t =>
      positiveReal_mul (positiveReal_boxPower hh n t) (positiveReal_unitBox hh (u - t))

theorem positiveReal_boxPlateau {A h r : ℝ} (hh : 0 < h) (hr : 0 < r) (n : ℕ) (u : ℝ) :
    0 ≤ (boxPlateau A h n r u).re ∧
      ((boxPlateau A h n r u).re : ℂ) = boxPlateau A h n r u := by
  rw [boxPlateau_apply]
  apply positiveReal_integral
  intro t
  apply positiveReal_mul (positiveReal_boxPower hh n t)
  rw [smoothUnitBump_eq hr, Complex.ofReal_re]
  exact ⟨(radiusBump hr).nonneg_normed _, rfl⟩

theorem integral_boxPower {A h : ℝ} (hA : 0 ≤ A) (hh : 0 < h) : ∀ n,
    ∫ u, boxPower A h n u = ((2 * A : ℝ) : ℂ)
  | 0 => by
    rw [boxPower_zero, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), Complex.real_smul]
    push_cast
    ring
  | n + 1 => by
    rw [boxPower_succ, integral_convolution (ContinuousLinearMap.mul ℝ ℂ)
      (integrable_boxPower A h n) (integrable_unitBox h)]
    simp only [ContinuousLinearMap.mul_apply', integral_boxPower hA hh n,
      integral_unitBox hh, mul_one]

theorem integrable_boxPlateau {A h r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (boxPlateau A h n r) :=
  (integrable_boxPower A h n).integrable_convolution _ (integrable_smoothUnitBump hr)

/-- Smoothing preserves the initial interval's mass, independently of order. -/
theorem integral_boxPlateau {A h r : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) : ∫ u, boxPlateau A h n r u = ((2 * A : ℝ) : ℂ) := by
  have hb : ∫ u, smoothUnitBump r u = 1 := by
    simp_rw [smoothUnitBump_eq hr]
    rw [integral_complex_ofReal, (radiusBump hr).integral_normed, Complex.ofReal_one]
  rw [boxPlateau, integral_convolution (ContinuousLinearMap.mul ℝ ℂ)
    (integrable_boxPower A h n) (integrable_smoothUnitBump hr)]
  simp only [ContinuousLinearMap.mul_apply', integral_boxPower hA hh n, hb, mul_one]

private theorem norm_eq_re_of_positiveReal {z : ℂ}
    (hz : 0 ≤ z.re ∧ (z.re : ℂ) = z) : ‖z‖ = z.re := by
  calc
    ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz.2.symm
    _ = z.re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1]

theorem integral_norm_unitBox {h : ℝ} (hh : 0 < h) : ∫ u, ‖unitBox h u‖ = 1 := by
  simp_rw [norm_eq_re_of_positiveReal (positiveReal_unitBox hh _)]
  have hi := integral_re (integrable_unitBox h)
  simp only [RCLike.re_to_complex] at hi
  rw [hi, integral_unitBox hh, Complex.one_re]

theorem integral_norm_boxPlateau {A h r : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) : ∫ u, ‖boxPlateau A h n r u‖ = 2 * A := by
  simp_rw [norm_eq_re_of_positiveReal (positiveReal_boxPlateau hh hr n _)]
  have hi := integral_re (integrable_boxPlateau (A := A) (h := h) hr n)
  simp only [RCLike.re_to_complex] at hi
  rw [hi, integral_boxPlateau hA hh hr, Complex.ofReal_re]

/-- The compact-support Fourier bound requires only integrability. -/
theorem norm_paperFT_le_mass_exp {f : ℝ → ℂ} {R : ℝ} (hf : Integrable f)
    (hs : ∀ u, f u ≠ 0 → |u| ≤ R) (z : ℂ) :
    ‖paperFT f z‖ ≤ (∫ u, ‖f u‖) * Real.exp (R * |z.im|) := by
  unfold paperFT
  calc
    _ ≤ ∫ u, ‖f u * Complex.exp (I * z * u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, ‖f u‖ * Real.exp (R * |z.im|) := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (hf.norm.mul_const _) (ae_of_all _ fun u => ?_)
      simp only
      by_cases hu : f u = 0
      · simp only [hu, zero_mul, norm_zero, le_refl]
      · rw [norm_mul, Complex.norm_exp]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        have he : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
        rw [he]
        calc
          -(z.im * u) ≤ |z.im * u| := neg_le_abs _
          _ = |u| * |z.im| := by rw [abs_mul, mul_comm]
          _ ≤ R * |z.im| := mul_le_mul_of_nonneg_right (hs u hu) (abs_nonneg _)
    _ = _ := integral_mul_const _ _

theorem norm_paperFT_unitBox_le_mass {h : ℝ} (hh : 0 < h) (z : ℂ) :
    ‖paperFT (unitBox h) z‖ ≤ Real.exp (h * |z.im|) := by
  have hb := norm_paperFT_le_mass_exp (integrable_unitBox h)
    (fun u hu => le_of_not_gt fun hn => hu (unitBox_eq_zero hn)) z
  simpa only [integral_norm_unitBox hh, one_mul] using hb

theorem norm_paperFT_boxPlateau_le_mass {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) (z : ℂ) :
    ‖paperFT (boxPlateau A h (n + 1) r) z‖ ≤
      2 * A * Real.exp (boxCameraRadius A h n r * |z.im|) := by
  have hb := norm_paperFT_le_mass_exp (integrable_boxPlateau hr (n + 1))
    (R := boxCameraRadius A h n r)
    (fun u hu => le_of_not_gt fun hn => hu (boxPlateau_eq_zero hh hr (n + 1) hn.le)) z
  simpa only [integral_norm_boxPlateau hA hh hr] using hb

end GaloisForLFunctions.MultiscaleMollifiedZetaField
