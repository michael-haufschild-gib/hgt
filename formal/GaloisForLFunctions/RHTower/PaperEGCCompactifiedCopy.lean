import GaloisForLFunctions.RHTower.PaperEGCVerticalMajorant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Compactifying the EGC imaginary observation axis

Homogeneous sine/cosine coordinates retain the literal correction at `t = tan (πθ)`.
The rational expression stays continuous through the projective point at infinity and has
value zero there. Its reciprocal-square copy budget is unchanged by compactification.
-/

namespace RHTower

noncomputable section
open scoped Topology

private theorem circle_factor_ne_zero (u : Set.Icc (-2 : ℝ) 2) (θ : ℝ) (q : XiZeroCopy) :
    (xiSpectralPoint q - ((u : ℝ) : ℂ)) * (Real.cos (Real.pi * θ) : ℂ) -
      Complex.I * (Real.sin (Real.pi * θ) : ℂ) ≠ 0 := by
  have hreal : (xiSpectralPoint q).re - (u : ℝ) ≠ 0 := by
    intro h
    have hgap := xiSpectral_re_sq_gt_thirtytwo q
    rw [sub_eq_zero.mp h] at hgap
    nlinarith [u.2.1, u.2.2]
  intro h
  have hre : ((xiSpectralPoint q).re - (u : ℝ)) * Real.cos (Real.pi * θ) = 0 := by
    simpa only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, Complex.zero_re]
      using congrArg Complex.re h
  have hc := (mul_eq_zero.mp hre).resolve_left hreal
  have hs : Real.sin (Real.pi * θ) = 0 := by
    have him := congrArg Complex.im h
    simpa only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, hc, mul_zero, zero_mul, mul_one,
      one_mul, add_zero, zero_add, sub_zero, zero_sub, neg_eq_zero, Complex.zero_im] using him
  have hcircle := Real.sin_sq_add_cos_sq (Real.pi * θ)
  simp [hc, hs] at hcircle

/-- The homogeneous denominator for the literal two prescribed shifted residues. -/
def paperEGCCircleDenominator (eps x : PaperEGCSmallParameter) (θ : ℝ) (q : XiZeroCopy) : ℂ :=
  ((xiSpectralPoint q - ((x : ℝ) : ℂ)) * (Real.cos (Real.pi * θ) : ℂ) -
    Complex.I * (Real.sin (Real.pi * θ) : ℂ))^2 -
      ((eps : ℝ) : ℂ)^2 * (Real.cos (Real.pi * θ) : ℂ)^2

/-- Both shifted factors remain nonzero, including the compactification point. -/
theorem paperEGCCircleDenominator_ne_zero (eps x : PaperEGCSmallParameter) (θ : ℝ)
    (q : XiZeroCopy) : paperEGCCircleDenominator eps x θ q ≠ 0 := by
  let up : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) + (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  let um : Set.Icc (-2 : ℝ) 2 := ⟨(x : ℝ) - (eps : ℝ), by
    constructor <;> linarith [x.2.1, x.2.2, eps.2.1, eps.2.2]⟩
  have he : paperEGCCircleDenominator eps x θ q =
      ((xiSpectralPoint q - ((um : ℝ) : ℂ)) * (Real.cos (Real.pi * θ) : ℂ) -
        Complex.I * (Real.sin (Real.pi * θ) : ℂ)) *
      ((xiSpectralPoint q - ((up : ℝ) : ℂ)) * (Real.cos (Real.pi * θ) : ℂ) -
        Complex.I * (Real.sin (Real.pi * θ) : ℂ)) := by
    simp only [paperEGCCircleDenominator, up, um]
    push_cast
    ring
  rw [he]
  exact mul_ne_zero (circle_factor_ne_zero um θ q) (circle_factor_ne_zero up θ q)

/-- One native correction in homogeneous coordinates on the compactified observation axis. -/
def paperEGCCircleCopy (eps x : PaperEGCSmallParameter) (θ : ℝ) (q : XiZeroCopy) : ℂ :=
  -(((eps : ℝ) : ℂ)^2 * (Real.cos (Real.pi * θ) : ℂ)^2) /
    paperEGCCircleDenominator eps x θ q

/-- At every finite chart point the compactified expression is the literal EGC correction. -/
theorem paperEGCCircleCopy_eq_line (eps x : PaperEGCSmallParameter) (θ : ℝ)
    (q : XiZeroCopy) (hc : Real.cos (Real.pi * θ) ≠ 0) :
    paperEGCCircleCopy eps x θ q = paperEGCLineCopy eps x (Real.tan (Real.pi * θ)) q := by
  let c : ℂ := Real.cos (Real.pi * θ)
  let s : ℂ := Real.sin (Real.pi * θ)
  let w : ℂ := ((x : ℝ) : ℂ) + (Real.tan (Real.pi * θ) : ℂ) * Complex.I
  have hc' : c ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have ht : (Real.tan (Real.pi * θ) : ℂ) = s / c := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  have hden : (xiSpectralPoint q - w)^2 - ((eps : ℝ) : ℂ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (paperEGC_line_plus_ne_zero eps x _ q)
      (paperEGC_line_minus_ne_zero eps x _ q)
  have he : paperEGCCircleDenominator eps x θ q =
      c^2 * ((xiSpectralPoint q - w)^2 - ((eps : ℝ) : ℂ)^2) := by
    change ((xiSpectralPoint q - ((x : ℝ) : ℂ)) * c - Complex.I * s)^2 -
      ((eps : ℝ) : ℂ)^2 * c^2 = _
    dsimp only [w]
    rw [ht]
    field_simp [hc']
    ring
  rw [paperEGCCircleCopy, he, paperEGCLineCopy,
    meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
      (eps : ℝ) _ _ (paperEGC_line_minus_ne_zero eps x _ q)
      (paperEGC_line_plus_ne_zero eps x _ q)]
  change -(((eps : ℝ) : ℂ)^2 * c^2) /
    (c^2 * ((xiSpectralPoint q - w)^2 - ((eps : ℝ) : ℂ)^2)) =
    -((eps : ℝ) : ℂ)^2 / ((xiSpectralPoint q - w)^2 - ((eps : ℝ) : ℂ)^2)
  field_simp [hc', hden]

/-- The prescribed infinity value is forced by the exact rational expression. -/
theorem paperEGCCircleCopy_eq_zero_of_cos_eq_zero (eps x : PaperEGCSmallParameter) (θ : ℝ)
    (q : XiZeroCopy) (hc : Real.cos (Real.pi * θ) = 0) :
    paperEGCCircleCopy eps x θ q = 0 := by
  simp [paperEGCCircleCopy, hc]

/-- Compactification preserves the uniform reciprocal-square majorant, with its shift factor. -/
theorem norm_paperEGCCircleCopy_le_scale (eps x : PaperEGCSmallParameter) (θ : ℝ)
    (q : XiZeroCopy) :
    ‖paperEGCCircleCopy eps x θ q‖ ≤ 8 * (eps : ℝ)^2 / ‖xiSpectralPoint q‖^2 := by
  by_cases hc : Real.cos (Real.pi * θ) = 0
  · rw [paperEGCCircleCopy_eq_zero_of_cos_eq_zero eps x θ q hc, norm_zero]
    positivity
  · rw [paperEGCCircleCopy_eq_line eps x θ q hc]
    exact norm_paperEGCLineCopy_le_scale eps x _ q

theorem norm_paperEGCCircleCopy_le (eps x : PaperEGCSmallParameter) (θ : ℝ) (q : XiZeroCopy) :
    ‖paperEGCCircleCopy eps x θ q‖ ≤ 8 / ‖xiSpectralPoint q‖^2 := by
  by_cases hc : Real.cos (Real.pi * θ) = 0
  · rw [paperEGCCircleCopy_eq_zero_of_cos_eq_zero eps x θ q hc, norm_zero]
    positivity
  · rw [paperEGCCircleCopy_eq_line eps x θ q hc]
    exact norm_paperEGCLineCopy_le eps x _ q

/-- Each copy extends continuously through infinity, without a pole or a discarded residue. -/
theorem continuous_paperEGCCircleCopy (eps x : PaperEGCSmallParameter) (q : XiZeroCopy) :
    Continuous (fun θ : ℝ => paperEGCCircleCopy eps x θ q) := by
  have hc : Continuous (fun θ : ℝ => (Real.cos (Real.pi * θ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hs : Continuous (fun θ : ℝ => (Real.sin (Real.pi * θ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  unfold paperEGCCircleCopy paperEGCCircleDenominator
  exact (continuous_const.mul (hc.pow 2)).neg.div
    ((((continuous_const.mul hc).sub (continuous_const.mul hs)).pow 2).sub
      (continuous_const.mul (hc.pow 2)))
    (fun θ => paperEGCCircleDenominator_ne_zero eps x θ q)

/-- One turn changes both homogeneous coordinates by sign and leaves every copy unchanged. -/
theorem paperEGCCircleCopy_periodic (eps x : PaperEGCSmallParameter) (q : XiZeroCopy) :
    Function.Periodic (fun θ => paperEGCCircleCopy eps x θ q) 1 := by
  intro θ
  have hangle : Real.pi * (θ + 1) = Real.pi * θ + Real.pi := by ring
  simp only [paperEGCCircleCopy, paperEGCCircleDenominator, hangle,
    Real.cos_add_pi, Real.sin_add_pi, Complex.ofReal_neg]
  ring_nf

end
end RHTower
