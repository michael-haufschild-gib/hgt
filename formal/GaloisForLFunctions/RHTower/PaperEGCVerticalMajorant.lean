import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairAllCopyCenteredCorrection
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# An all-copy majorant for the EGC correction on vertical observation lines

The certified spectral real-part gap keeps every prescribed shifted pole away from the
fixed source window `|Re w| ≤ 1`, for every imaginary height and every shift `|eps| ≤ 1`.
Reciprocal-square summability then pays for the complete multiplicity-copy correction row.
-/

namespace RHTower

noncomputable section
open Complex Filter
open scoped Topology

/-- Prescribed shifts and real observation offsets in the fixed source window. -/
abbrev PaperEGCSmallParameter := Set.Icc (-1 : ℝ) 1

private theorem spectral_abs_re_gt_four (q : XiZeroCopy) :
    (4 : ℝ) < |(xiSpectralPoint q).re| := by
  have h := xiSpectral_re_sq_gt_thirtytwo q
  nlinarith [sq_abs (xiSpectralPoint q).re, abs_nonneg (xiSpectralPoint q).re]

/-- The full vertical line stays quantitatively away from every shifted spectral pole. -/
theorem paperEGC_pole_norm_lower (u : Set.Icc (-2 : ℝ) 2) (t : ℝ) (q : XiZeroCopy) :
    |(xiSpectralPoint q).re| / 2 ≤
      ‖xiSpectralPoint q - ((u : ℝ) : ℂ) - (t : ℂ) * Complex.I‖ := by
  have hu : |(u : ℝ)| ≤ 2 := abs_le.mpr u.2
  have htri := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re (u : ℝ)
  have hlo : |(xiSpectralPoint q).re| / 2 ≤ |(xiSpectralPoint q).re - (u : ℝ)| := by
    have hfour := spectral_abs_re_gt_four q
    linarith
  have hre : (xiSpectralPoint q - ((u : ℝ) : ℂ) - (t : ℂ) * Complex.I).re =
      (xiSpectralPoint q).re - (u : ℝ) := by simp
  exact hlo.trans (by simpa only [hre] using
    Complex.abs_re_le_norm (xiSpectralPoint q - ((u : ℝ) : ℂ) - (t : ℂ) * Complex.I))

/-- Pole avoidance is derived from the native spectral gap, uniformly in imaginary height. -/
theorem paperEGC_pole_ne_zero (u : Set.Icc (-2 : ℝ) 2) (t : ℝ) (q : XiZeroCopy) :
    xiSpectralPoint q - ((u : ℝ) : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
  apply norm_pos_iff.mp
  have hfour := spectral_abs_re_gt_four q
  exact (by linarith : (0 : ℝ) < |(xiSpectralPoint q).re| / 2).trans_le
    (paperEGC_pole_norm_lower u t q)

/-- The literal native correction of one copy on a prescribed vertical observation line. -/
def paperEGCLineCopy (eps x : PaperEGCSmallParameter) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  meromorphicCauchyPairShiftResidueCorrection (eps : ℝ)
    (((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) (xiSpectralPoint q)

theorem paperEGC_line_minus_ne_zero (eps x : PaperEGCSmallParameter) (t : ℝ) (q : XiZeroCopy) :
    xiSpectralPoint q - (((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((eps : ℝ) : ℂ) ≠ 0 := by
  let u : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) + (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  convert paperEGC_pole_ne_zero u t q using 1
  simp only [u]
  push_cast
  ring_nf

theorem paperEGC_line_plus_ne_zero (eps x : PaperEGCSmallParameter) (t : ℝ) (q : XiZeroCopy) :
    xiSpectralPoint q - (((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) + ((eps : ℝ) : ℂ) ≠ 0 := by
  let u : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) - (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  convert paperEGC_pole_ne_zero u t q using 1
  simp only [u]
  push_cast
  ring_nf

/-- The quadratic small-shift factor survives the uniform copy majorant. -/
theorem norm_paperEGCLineCopy_le_scale (eps x : PaperEGCSmallParameter) (t : ℝ) (q : XiZeroCopy) :
    ‖paperEGCLineCopy eps x t q‖ ≤
      8 * (eps : ℝ)^2 / ‖xiSpectralPoint q‖^2 := by
  let a := xiSpectralPoint q
  let w : ℂ := ((x : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let up : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) + (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  let um : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) - (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  have hm : |a.re| / 2 ≤ ‖a - w - ((eps : ℝ) : ℂ)‖ := by
    convert paperEGC_pole_norm_lower up t q using 1
    simp only [up, a, w]
    push_cast
    ring_nf
  have hp : |a.re| / 2 ≤ ‖a - w + ((eps : ℝ) : ℂ)‖ := by
    convert paperEGC_pole_norm_lower um t q using 1
    simp only [um, a, w]
    push_cast
    ring_nf
  have hprod := mul_le_mul hp hm (by positivity : (0 : ℝ) ≤ |a.re| / 2)
    (norm_nonneg (a - w + ((eps : ℝ) : ℂ)))
  have hsq : ‖a‖^2 = a.re^2 + a.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hgap := xiSpectral_re_sq_gt_thirtytwo q
  have hstrip := xiSpectralPoint_im_sq_lt_quarter q
  have hbound : ‖a‖^2 ≤
      8 * (‖a - w + ((eps : ℝ) : ℂ)‖ * ‖a - w - ((eps : ℝ) : ℂ)‖) := by
    change 32 < a.re^2 at hgap
    change a.im^2 < 1/4 at hstrip
    nlinarith [sq_abs a.re]
  have hminus := paperEGC_line_minus_ne_zero eps x t q
  have hplus := paperEGC_line_plus_ne_zero eps x t q
  have hpos : 0 < ‖a - w + ((eps : ℝ) : ℂ)‖ * ‖a - w - ((eps : ℝ) : ℂ)‖ :=
    mul_pos (norm_pos_iff.mpr hplus) (norm_pos_iff.mpr hminus)
  rw [paperEGCLineCopy, meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
    (eps : ℝ) _ _ hminus hplus, norm_div, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, sq_sub_sq, norm_mul]
  rw [div_le_div_iff₀ hpos (sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)))]
  nlinarith [mul_le_mul_of_nonneg_left hbound (sq_nonneg (eps : ℝ))]

/-- One summable budget controls every allowed shift, real offset and imaginary height. -/
theorem norm_paperEGCLineCopy_le (eps x : PaperEGCSmallParameter) (t : ℝ) (q : XiZeroCopy) :
    ‖paperEGCLineCopy eps x t q‖ ≤ 8 / ‖xiSpectralPoint q‖^2 := by
  have heps : (eps : ℝ)^2 ≤ 1 := by nlinarith [eps.2.1, eps.2.2]
  exact (norm_paperEGCLineCopy_le_scale eps x t q).trans
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

/-- The complete native multiplicity-copy row is absolutely summable at every observation. -/
theorem summable_norm_paperEGCLineCopy (eps x : PaperEGCSmallParameter) (t : ℝ) :
    Summable (fun q : XiZeroCopy => ‖paperEGCLineCopy eps x t q‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => norm_paperEGCLineCopy_le eps x t q)
  simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8

end
end RHTower
