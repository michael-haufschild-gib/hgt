import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Explicit rectangular two-edge Weil profiles

This module supplies the unconditional scalar foundation for a possible cofinal
Connes--Consani--Moscovici test family.  The bilateral rectangular profile has
an elementary Laplace transform whose right-half-plane carrier never vanishes.
Its square separates exactly into a growing edge, a fixed middle edge, and a
decaying edge.  No RH implication is asserted here.
-/

open Complex ComplexConjugate

namespace RHTower

noncomputable section

/-- The Laplace amplitude of a real interval of length `L`, with its removable
value at the origin filled in. -/
def rectangularWindowAmplitude (L : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then L else (1 - Complex.exp (-(L : ℂ) * w)) / w

/-- The bilateral transform of two length-`L` rectangles placed at the two
edges `a` and `-a`. -/
def rectangularTwoEdgeTransform (L a : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w +
    Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)

@[simp] theorem rectangularWindowAmplitude_zero (L : ℝ) :
    rectangularWindowAmplitude L 0 = L := by
  simp [rectangularWindowAmplitude]

theorem rectangularWindowAmplitude_eq_div {L : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularWindowAmplitude L w =
      (1 - Complex.exp (-(L : ℂ) * w)) / w := by
  simp [rectangularWindowAmplitude, hw]

/-- A positive-length rectangular window has no Laplace-amplitude zero in the
open right half-plane. -/
theorem rectangularWindowAmplitude_ne_zero
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hwre : 0 < w.re) :
    rectangularWindowAmplitude L w ≠ 0 := by
  have hw : w ≠ 0 := by
    intro h
    rw [h] at hwre
    simp at hwre
  rw [rectangularWindowAmplitude_eq_div hw]
  intro hzero
  have hnum : 1 - Complex.exp (-(L : ℂ) * w) = 0 := by
    exact (div_eq_zero_iff).mp hzero |>.resolve_right hw
  have hexp : Complex.exp (-(L : ℂ) * w) = 1 := by
    exact (sub_eq_zero.mp hnum).symm
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff] at hnorm
  have hre : (-(L : ℂ) * w).re = -L * w.re := by
    simp [Complex.mul_re]
  rw [hre] at hnorm
  nlinarith

/-- Reversing the spectral coordinate multiplies the nonzero-window amplitude
by the exact length exponential. -/
theorem rectangularWindowAmplitude_neg
    {L : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularWindowAmplitude L (-w) =
      Complex.exp ((L : ℂ) * w) * rectangularWindowAmplitude L w := by
  rw [rectangularWindowAmplitude_eq_div (neg_ne_zero.mpr hw),
    rectangularWindowAmplitude_eq_div hw]
  field_simp [hw]
  have hinv : Complex.exp ((L : ℂ) * w) *
      Complex.exp (-(L : ℂ) * w) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    -(1 - Complex.exp ((L : ℂ) * w)) =
        Complex.exp ((L : ℂ) * w) - 1 := by ring
    _ = Complex.exp ((L : ℂ) * w) -
        Complex.exp ((L : ℂ) * w) * Complex.exp (-(L : ℂ) * w) := by
      rw [hinv]
    _ = Complex.exp ((L : ℂ) * w) *
        (1 - Complex.exp (-((L : ℂ) * w))) := by
      rw [show -((L : ℂ) * w) = -(L : ℂ) * w by ring]
      ring

/-- The window amplitude respects Schwarz conjugation. -/
theorem rectangularWindowAmplitude_conj (L : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (rectangularWindowAmplitude L w) =
      rectangularWindowAmplitude L ((starRingEnd ℂ) w) := by
  by_cases hw : w = 0
  · subst w
    simp
  · have hcw : (starRingEnd ℂ) w ≠ 0 := star_ne_zero.mpr hw
    rw [rectangularWindowAmplitude_eq_div hw,
      rectangularWindowAmplitude_eq_div hcw]
    change conj ((1 - Complex.exp (-(L : ℂ) * w)) / w) =
      (1 - Complex.exp (-(L : ℂ) * conj w)) / conj w
    rw [map_div₀, map_sub, map_one]
    rw [← Complex.exp_conj]
    congr 3
    simp

/-- The bilateral transform respects Schwarz conjugation. -/
theorem rectangularTwoEdgeTransform_conj (L a : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (rectangularTwoEdgeTransform L a w) =
      rectangularTwoEdgeTransform L a ((starRingEnd ℂ) w) := by
  rw [rectangularTwoEdgeTransform, rectangularTwoEdgeTransform]
  simp only [map_add, map_mul, map_neg, rectangularWindowAmplitude_conj]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  congr 1 <;> simp

/-- The bilateral two-edge transform is even. -/
theorem rectangularTwoEdgeTransform_even (L a : ℝ) (w : ℂ) :
    rectangularTwoEdgeTransform L a (-w) = rectangularTwoEdgeTransform L a w := by
  rw [rectangularTwoEdgeTransform, rectangularTwoEdgeTransform]
  simp only [neg_neg]
  ring_nf

/-- The rectangular two-edge transform as a function of the centered Xi
spectral coordinate. -/
def xiRectangularTwoEdgeTransform (L a : ℝ) (z : ℂ) : ℂ :=
  rectangularTwoEdgeTransform L a (I * z)

/-- The Xi-Weil involution fixes the real rectangular two-edge transform. -/
theorem xiWeilSharp_xiRectangularTwoEdgeTransform (L a : ℝ) (z : ℂ) :
    xiWeilSharp (xiRectangularTwoEdgeTransform L a) z =
      xiRectangularTwoEdgeTransform L a z := by
  rw [xiWeilSharp, xiRectangularTwoEdgeTransform,
    rectangularTwoEdgeTransform_conj]
  rw [show (starRingEnd ℂ) (I * (starRingEnd ℂ) z) = -(I * z) by simp]
  exact rectangularTwoEdgeTransform_even L a (I * z)

/-- Away from the removable point, the bilateral transform factors into one
window amplitude and two edge exponentials. -/
theorem rectangularTwoEdgeTransform_eq
    {L a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularTwoEdgeTransform L a w = rectangularWindowAmplitude L w *
      (Complex.exp ((a : ℂ) * w) + Complex.exp (-(a - L : ℂ) * w)) := by
  rw [rectangularTwoEdgeTransform, rectangularWindowAmplitude_neg hw]
  have he : Complex.exp (-(a : ℂ) * w) * Complex.exp ((L : ℂ) * w) =
      Complex.exp (-(a - L : ℂ) * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w +
        Complex.exp (-(a : ℂ) * w) *
          (Complex.exp ((L : ℂ) * w) * rectangularWindowAmplitude L w) =
      rectangularWindowAmplitude L w *
        (Complex.exp ((a : ℂ) * w) +
          Complex.exp (-(a : ℂ) * w) * Complex.exp ((L : ℂ) * w)) := by ring
    _ = _ := by rw [he]

/-- Exact three-edge square decomposition.  This is the algebraic input needed
to isolate the growing right-half-plane contribution in a cofinal argument. -/
theorem rectangularTwoEdgeTransform_sq_decomposition
    {L a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularTwoEdgeTransform L a w ^ 2 = rectangularWindowAmplitude L w ^ 2 *
      (Complex.exp (2 * (a : ℂ) * w) + 2 * Complex.exp ((L : ℂ) * w) +
        Complex.exp (-2 * (a - L : ℂ) * w)) := by
  rw [rectangularTwoEdgeTransform_eq hw]
  rw [mul_pow]
  congr 1
  rw [add_sq]
  have hleft : Complex.exp ((a : ℂ) * w) ^ 2 =
      Complex.exp (2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hmid : Complex.exp ((a : ℂ) * w) *
      Complex.exp (-(a - L : ℂ) * w) = Complex.exp ((L : ℂ) * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright : Complex.exp (-(a - L : ℂ) * w) ^ 2 =
      Complex.exp (-2 * (a - L : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [hleft, hright]
  calc
    Complex.exp (2 * (a : ℂ) * w) +
        2 * Complex.exp ((a : ℂ) * w) * Complex.exp (-(a - L : ℂ) * w) +
        Complex.exp (-2 * (a - L : ℂ) * w) =
      Complex.exp (2 * (a : ℂ) * w) +
        2 * (Complex.exp ((a : ℂ) * w) *
          Complex.exp (-(a - L : ℂ) * w)) +
        Complex.exp (-2 * (a - L : ℂ) * w) := by ring
    _ = _ := by rw [hmid]

/-! ## Uniform Xi-divisor summability -/

private theorem real_mul_re_le_abs_half {c : ℝ} {w : ℂ}
    (hw : |w.re| ≤ (1 / 2 : ℝ)) :
    ((c : ℂ) * w).re ≤ |c| / 2 := by
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    c * w.re ≤ |c * w.re| := le_abs_self _
    _ = |c| * |w.re| := abs_mul c w.re
    _ ≤ |c| * (1 / 2) := by
      exact mul_le_mul_of_nonneg_left hw (abs_nonneg c)
    _ = |c| / 2 := by ring

/-- On the centered critical strip, a rectangular-window amplitude is bounded
by an explicit constant times the reciprocal spectral height. -/
theorem norm_rectangularWindowAmplitude_le
    (L : ℝ) {w : ℂ} (hw : w ≠ 0) (hwre : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularWindowAmplitude L w‖ ≤
      (1 + Real.exp (|L| / 2)) / ‖w‖ := by
  rw [rectangularWindowAmplitude_eq_div hw, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg w)
  calc
    ‖1 - Complex.exp (-(L : ℂ) * w)‖ ≤
        ‖(1 : ℂ)‖ + ‖Complex.exp (-(L : ℂ) * w)‖ := norm_sub_le _ _
    _ = 1 + Real.exp ((-(L : ℂ) * w).re) := by
      rw [norm_one, Complex.norm_exp]
    _ ≤ 1 + Real.exp (|L| / 2) := by
      gcongr
      simpa only [ofReal_neg, neg_mul, abs_neg] using
        (real_mul_re_le_abs_half (c := -L) (w := w) hwre)

/-- The entire two-edge transform has a uniform `O(1 / ‖w‖)` bound throughout
the centered critical strip. -/
theorem norm_rectangularTwoEdgeTransform_le
    (L a : ℝ) {w : ℂ} (hw : w ≠ 0) (hwre : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularTwoEdgeTransform L a w‖ ≤
      ((1 + Real.exp (|L| / 2)) *
        (Real.exp (|a| / 2) + Real.exp (|a - L| / 2))) / ‖w‖ := by
  rw [rectangularTwoEdgeTransform_eq hw, norm_mul]
  calc
    ‖rectangularWindowAmplitude L w‖ *
        ‖Complex.exp ((a : ℂ) * w) + Complex.exp (-(a - L : ℂ) * w)‖ ≤
      ((1 + Real.exp (|L| / 2)) / ‖w‖) *
        (‖Complex.exp ((a : ℂ) * w)‖ +
          ‖Complex.exp (-(a - L : ℂ) * w)‖) := by
      gcongr
      · exact norm_rectangularWindowAmplitude_le L hw hwre
      · exact norm_add_le _ _
    _ ≤ ((1 + Real.exp (|L| / 2)) / ‖w‖) *
        (Real.exp (|a| / 2) + Real.exp (|a - L| / 2)) := by
      gcongr
      · rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (real_mul_re_le_abs_half hwre)
      · rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (by
          simpa only [ofReal_neg, ofReal_sub, neg_mul, abs_neg] using
            (real_mul_re_le_abs_half (c := -(a - L)) (w := w) hwre))
    _ = _ := by
      field_simp

/-- Multiplication by `i` converts the centered Xi spectral coordinate back to
the literal displacement `rho - 1/2`. -/
theorem I_mul_xiSpectralPoint (q : XiZeroCopy) :
    I * xiSpectralPoint q = (q.1 : ℂ) - 1 / 2 := by
  rw [xiSpectralPoint]
  have hI : I * (-I) = (1 : ℂ) := by
    rw [mul_neg, I_mul_I]
    ring
  calc
    I * (((q.1 : ℂ) - 1 / 2) * (-I)) =
        ((q.1 : ℂ) - 1 / 2) * (I * (-I)) := by ring
    _ = (q.1 : ℂ) - 1 / 2 := by rw [hI, mul_one]

/-- Every multiplicity copy of a Xi zero lies strictly inside the half-width
strip in the rectangular transform coordinate. -/
theorem abs_re_I_mul_xiSpectralPoint_le_half (q : XiZeroCopy) :
    |(I * xiSpectralPoint q).re| < (1 / 2 : ℝ) := by
  rw [I_mul_xiSpectralPoint]
  simp only [Complex.sub_re]
  norm_num
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_lt]
  constructor <;> linarith

/-- Pointwise domination of every rectangular two-edge Xi value by the
reciprocal-square canonical-product majorant. -/
theorem xiRectangularTwoEdgeTransform_square_le
    (L a : ℝ) (q : XiZeroCopy) :
    ‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)‖ ^ 2 ≤
      ((1 + Real.exp (|L| / 2)) *
        (Real.exp (|a| / 2) + Real.exp (|a - L| / 2))) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let C : ℝ := (1 + Real.exp (|L| / 2)) *
    (Real.exp (|a| / 2) + Real.exp (|a - L| / 2))
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  have hbound : ‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)‖ ≤
      C / ‖xiSpectralPoint q‖ := by
    rw [xiRectangularTwoEdgeTransform]
    have h := norm_rectangularTwoEdgeTransform_le L a hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
    rw [norm_mul, norm_I, one_mul] at h
    exact h
  calc
    ‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)‖ ^ 2 ≤
        (C / ‖xiSpectralPoint q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      field_simp

/-- Every explicit rectangular two-edge profile is square-summable on the
actual multiplicity-exact Xi divisor. -/
theorem xiRectangularTwoEdgeTransform_squareSummable (L a : ℝ) :
    XiWeilSquareSummable (xiRectangularTwoEdgeTransform L a) := by
  let C : ℝ := (1 + Real.exp (|L| / 2)) *
    (Real.exp (|a| / 2) + Real.exp (|a - L| / 2))
  apply Summable.of_nonneg_of_le
  · intro q
    positivity
  · intro q
    exact xiRectangularTwoEdgeTransform_square_le L a q
  · exact xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)

end

end RHTower
