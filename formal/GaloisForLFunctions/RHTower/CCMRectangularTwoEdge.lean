import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.WindingXiCircle

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

/-! ## Dominant edge and bounded-remainder decomposition -/

/-- The exponentially growing edge selected by the sign of the transverse
coordinate.  It vanishes on the critical line. -/
def rectangularTwoEdgeDominant (L a : ℝ) (w : ℂ) : ℂ :=
  if 0 < w.re then
    rectangularWindowAmplitude L w ^ 2 * Complex.exp (2 * (a : ℂ) * w)
  else if w.re < 0 then
    rectangularWindowAmplitude L (-w) ^ 2 * Complex.exp (-2 * (a : ℂ) * w)
  else 0

/-- A uniform strip majorant for the non-growing part of the squared two-edge
transform. -/
def rectangularTwoEdgeRemainderBound (L : ℝ) : ℝ :=
  (1 + Real.exp (|L| / 2)) ^ 2 * (2 * Real.exp (|L| / 2) + 4)

/-- At logarithmic aperture `a=(log n)/2`, the positive growing edge becomes
the ordinary Dirichlet monomial `n^w`. -/
theorem rectangularTwoEdgeDominant_logSample_of_pos
    {L : ℝ} {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hwre : 0 < w.re) :
    rectangularTwoEdgeDominant L (Real.log n / 2) w =
      rectangularWindowAmplitude L w ^ 2 * (n : ℂ) ^ w := by
  rw [rectangularTwoEdgeDominant, if_pos hwre]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  congr 1
  push_cast
  ring

/-- At the same logarithmic aperture, the negative growing edge is the
reflected monomial `n^(-w)`. -/
theorem rectangularTwoEdgeDominant_logSample_of_neg
    {L : ℝ} {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hwre : w.re < 0) :
    rectangularTwoEdgeDominant L (Real.log n / 2) w =
      rectangularWindowAmplitude L (-w) ^ 2 * (n : ℂ) ^ (-w) := by
  rw [rectangularTwoEdgeDominant, if_neg (not_lt.mpr hwre.le), if_pos hwre]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  congr 1
  push_cast
  ring

/-- The sign-selected dominant edge is even. -/
theorem rectangularTwoEdgeDominant_even (L a : ℝ) (w : ℂ) :
    rectangularTwoEdgeDominant L a (-w) = rectangularTwoEdgeDominant L a w := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hneg
    rw [rectangularTwoEdgeDominant, if_pos hnpos,
      rectangularTwoEdgeDominant, if_neg (not_lt.mpr hneg.le), if_pos hneg]
    rw [show 2 * (a : ℂ) * (-w) = -2 * (a : ℂ) * w by ring]
  · have hnzero : (-w).re = 0 := by simpa using congrArg Neg.neg hzero
    rw [rectangularTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith),
      rectangularTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith)]
  · have hnneg : (-w).re < 0 := by simpa using neg_lt_zero.mpr hpos
    rw [rectangularTwoEdgeDominant, if_neg (not_lt.mpr hnneg.le), if_pos hnneg,
      rectangularTwoEdgeDominant, if_pos hpos]
    rw [show -2 * (a : ℂ) * (-w) = 2 * (a : ℂ) * w by ring]
    simp only [neg_neg]

/-- The sign-selected dominant edge respects Schwarz conjugation. -/
theorem rectangularTwoEdgeDominant_conj (L a : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (rectangularTwoEdgeDominant L a w) =
      rectangularTwoEdgeDominant L a ((starRingEnd ℂ) w) := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · have hcneg : ((starRingEnd ℂ) w).re < 0 := by simpa using hneg
    rw [rectangularTwoEdgeDominant, if_neg (not_lt.mpr hneg.le), if_pos hneg,
      rectangularTwoEdgeDominant, if_neg (not_lt.mpr hcneg.le), if_pos hcneg,
      map_mul, map_pow, rectangularWindowAmplitude_conj, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_neg, Complex.conj_ofReal, map_ofNat]
  · have hczero : ((starRingEnd ℂ) w).re = 0 := by simpa using hzero
    rw [rectangularTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith),
      rectangularTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith), map_zero]
  · have hcpos : 0 < ((starRingEnd ℂ) w).re := by simpa using hpos
    rw [rectangularTwoEdgeDominant, if_pos hpos,
      rectangularTwoEdgeDominant, if_pos hcpos,
      map_mul, map_pow, rectangularWindowAmplitude_conj, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, map_ofNat]

/-- Exact positive-transverse decomposition after removing the growing edge. -/
theorem rectangularTwoEdgeTransform_sq_sub_dominant_of_pos
    {L a : ℝ} {w : ℂ} (hwre : 0 < w.re) :
    rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w =
      rectangularWindowAmplitude L w ^ 2 *
        (2 * Complex.exp ((L : ℂ) * w) +
          Complex.exp (-2 * (a - L : ℂ) * w)) := by
  have hw : w ≠ 0 := by
    intro h
    rw [h] at hwre
    simp at hwre
  rw [rectangularTwoEdgeTransform_sq_decomposition hw,
    rectangularTwoEdgeDominant, if_pos hwre]
  ring

/-- Exact negative-transverse decomposition after removing the reflected
growing edge. -/
theorem rectangularTwoEdgeTransform_sq_sub_dominant_of_neg
    {L a : ℝ} {w : ℂ} (hwre : w.re < 0) :
    rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w =
      rectangularWindowAmplitude L (-w) ^ 2 *
        (2 * Complex.exp ((L : ℂ) * (-w)) +
          Complex.exp (-2 * (a - L : ℂ) * (-w))) := by
  have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hwre
  rw [rectangularTwoEdgeDominant, if_neg (not_lt.mpr hwre.le), if_pos hwre]
  rw [← rectangularTwoEdgeTransform_even L a w]
  have h := rectangularTwoEdgeTransform_sq_sub_dominant_of_pos
    (L := L) (a := a) (w := -w) hnpos
  rw [rectangularTwoEdgeDominant, if_pos hnpos] at h
  rw [show 2 * (a : ℂ) * (-w) = -2 * (a : ℂ) * w by ring] at h
  simpa only [neg_neg] using h

/-- On the critical line the selected dominant edge is zero. -/
@[simp] theorem rectangularTwoEdgeDominant_of_re_eq_zero
    (L a : ℝ) {w : ℂ} (hwre : w.re = 0) :
    rectangularTwoEdgeDominant L a w = 0 := by
  rw [rectangularTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith)]

/-- In the positive transverse half-strip, the squared transform after removal
of its growing edge is uniformly `O(1/‖w‖²)` in the aperture `a>=L`. -/
theorem norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_pos_le
    {L a : ℝ} {w : ℂ} (ha : L ≤ a) (hwre : 0 < w.re)
    (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w‖ ≤
      rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
  have hw : w ≠ 0 := by
    intro h
    rw [h] at hwre
    simp at hwre
  rw [rectangularTwoEdgeTransform_sq_sub_dominant_of_pos hwre,
    norm_mul, norm_pow]
  have hA := norm_rectangularWindowAmplitude_le L hw hstrip
  have hA2 : ‖rectangularWindowAmplitude L w‖ ^ 2 ≤
      ((1 + Real.exp (|L| / 2)) / ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hLexp : ‖Complex.exp ((L : ℂ) * w)‖ ≤ Real.exp (|L| / 2) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (real_mul_re_le_abs_half hstrip)
  have hdecRe : (-2 * (a - L : ℂ) * w).re ≤ 0 := by
    norm_num [Complex.mul_re]
    nlinarith
  have hdec : ‖Complex.exp (-2 * (a - L : ℂ) * w)‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hdecRe
  have hinner :
      ‖2 * Complex.exp ((L : ℂ) * w) +
          Complex.exp (-2 * (a - L : ℂ) * w)‖ ≤
        2 * Real.exp (|L| / 2) + 1 := by
    calc
      ‖2 * Complex.exp ((L : ℂ) * w) +
          Complex.exp (-2 * (a - L : ℂ) * w)‖ ≤
          ‖2 * Complex.exp ((L : ℂ) * w)‖ +
            ‖Complex.exp (-2 * (a - L : ℂ) * w)‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp (|L| / 2) + 1 := by
        rw [norm_mul, norm_ofNat]
        gcongr
  calc
    ‖rectangularWindowAmplitude L w‖ ^ 2 *
        ‖2 * Complex.exp ((L : ℂ) * w) +
          Complex.exp (-2 * (a - L : ℂ) * w)‖ ≤
      ((1 + Real.exp (|L| / 2)) / ‖w‖) ^ 2 *
        (2 * Real.exp (|L| / 2) + 1) := by gcongr
    _ ≤ ((1 + Real.exp (|L| / 2)) / ‖w‖) ^ 2 *
        (2 * Real.exp (|L| / 2) + 4) := by
      gcongr
      norm_num
    _ = rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
      rw [rectangularTwoEdgeRemainderBound]
      field_simp

/-- The negative transverse half-strip has the same uniform remainder bound by
functional-equation reflection. -/
theorem norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_neg_le
    {L a : ℝ} {w : ℂ} (ha : L ≤ a) (hwre : w.re < 0)
    (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w‖ ≤
      rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
  have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hwre
  have hnstrip : |(-w).re| ≤ (1 / 2 : ℝ) := by simpa using hstrip
  have h := norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_pos_le
    (L := L) (a := a) (w := -w) ha hnpos hnstrip
  rw [rectangularTwoEdgeTransform_sq_sub_dominant_of_pos hnpos] at h
  rw [rectangularTwoEdgeTransform_sq_sub_dominant_of_neg hwre]
  simpa only [norm_neg] using h

/-- On the critical line the entire squared transform is uniformly
`O(1/‖w‖²)` because all aperture exponentials have unit norm. -/
theorem norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_re_eq_zero_le
    {L a : ℝ} {w : ℂ} (hw : w ≠ 0) (hwre : w.re = 0) :
    ‖rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w‖ ≤
      rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
  rw [rectangularTwoEdgeDominant_of_re_eq_zero L a hwre, sub_zero, norm_pow]
  have hstrip : |w.re| ≤ (1 / 2 : ℝ) := by rw [hwre]; norm_num
  have hnstrip : |(-w).re| ≤ (1 / 2 : ℝ) := by simpa using hstrip
  have hA := norm_rectangularWindowAmplitude_le L hw hstrip
  have hAn := norm_rectangularWindowAmplitude_le L (neg_ne_zero.mpr hw) hnstrip
  rw [norm_neg] at hAn
  have hpa : ‖Complex.exp ((a : ℂ) * w)‖ = 1 := by
    rw [Complex.norm_exp, show ((a : ℂ) * w).re = 0 by
      simp [Complex.mul_re, hwre]]
    exact Real.exp_zero
  have hna : ‖Complex.exp (-(a : ℂ) * w)‖ = 1 := by
    rw [Complex.norm_exp, show (-(a : ℂ) * w).re = 0 by
      simp [Complex.mul_re, hwre]]
    exact Real.exp_zero
  have hF : ‖rectangularTwoEdgeTransform L a w‖ ≤
      2 * (1 + Real.exp (|L| / 2)) / ‖w‖ := by
    rw [rectangularTwoEdgeTransform]
    calc
      ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w +
          Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)‖ ≤
        ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w‖ +
          ‖Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)‖ :=
        norm_add_le _ _
      _ ≤ (1 + Real.exp (|L| / 2)) / ‖w‖ +
          (1 + Real.exp (|L| / 2)) / ‖w‖ := by
        rw [norm_mul, norm_mul, hpa, hna, one_mul, one_mul]
        gcongr
      _ = 2 * (1 + Real.exp (|L| / 2)) / ‖w‖ := by ring
  have hF2 : ‖rectangularTwoEdgeTransform L a w‖ ^ 2 ≤
      (2 * (1 + Real.exp (|L| / 2)) / ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hF 2
  calc
    ‖rectangularTwoEdgeTransform L a w‖ ^ 2 ≤
        (2 * (1 + Real.exp (|L| / 2)) / ‖w‖) ^ 2 := hF2
    _ ≤ rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
      rw [rectangularTwoEdgeRemainderBound]
      have hwNorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      field_simp
      have hexp : 0 < Real.exp (|L| / 2) := Real.exp_pos _
      nlinarith [sq_nonneg (1 + Real.exp (|L| / 2))]

/-- Uniform remainder bound on the whole centered critical strip. -/
theorem norm_rectangularTwoEdgeTransform_sq_sub_dominant_le
    {L a : ℝ} {w : ℂ} (ha : L ≤ a) (hw : w ≠ 0)
    (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularTwoEdgeTransform L a w ^ 2 - rectangularTwoEdgeDominant L a w‖ ≤
      rectangularTwoEdgeRemainderBound L / ‖w‖ ^ 2 := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · exact norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_neg_le ha hneg hstrip
  · exact norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_re_eq_zero_le hw hzero
  · exact norm_rectangularTwoEdgeTransform_sq_sub_dominant_of_pos_le ha hpos hstrip

/-- Dominant edge in the centered Xi spectral coordinate. -/
def xiRectangularTwoEdgeDominant (L a : ℝ) (z : ℂ) : ℂ :=
  rectangularTwoEdgeDominant L a (I * z)

/-- The multiplicity-exact Xi remainder term after removing the selected
growing edge. -/
def xiRectangularTwoEdgeRemainderTerm (L a : ℝ) (q : XiZeroCopy) : ℂ :=
  xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 -
    xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)

/-- Every Xi remainder term is dominated by the canonical reciprocal-square
majorant, uniformly for `a>=L`. -/
theorem norm_xiRectangularTwoEdgeRemainderTerm_le
    {L a : ℝ} (ha : L ≤ a) (q : XiZeroCopy) :
    ‖xiRectangularTwoEdgeRemainderTerm L a q‖ ≤
      rectangularTwoEdgeRemainderBound L / ‖xiSpectralPoint q‖ ^ 2 := by
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  have h := norm_rectangularTwoEdgeTransform_sq_sub_dominant_le
    (L := L) (a := a) (w := I * xiSpectralPoint q) ha hz
    (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
  rw [norm_mul, norm_I, one_mul] at h
  simpa only [xiRectangularTwoEdgeRemainderTerm,
    xiRectangularTwoEdgeTransform, xiRectangularTwoEdgeDominant] using h

/-- The full multiplicity-exact remainder series is absolutely summable for
every aperture `a>=L`. -/
theorem xiRectangularTwoEdgeRemainderTerm_summable
    {L a : ℝ} (ha : L ≤ a) :
    Summable (xiRectangularTwoEdgeRemainderTerm L a) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      (rectangularTwoEdgeRemainderBound L))
  intro q
  calc
    ‖xiRectangularTwoEdgeRemainderTerm L a q‖ ≤
        rectangularTwoEdgeRemainderBound L / ‖xiSpectralPoint q‖ ^ 2 :=
      norm_xiRectangularTwoEdgeRemainderTerm_le ha q
    _ = rectangularTwoEdgeRemainderBound L *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- The zero-side polarization of a rectangular test is literally the sum of
its squared values, because the test is fixed by `xiWeilSharp`. -/
theorem xiWeilPolarization_rectangular_eq_tsum_sq (L a : ℝ) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      ∑' q : XiZeroCopy,
        xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp_xiRectangularTwoEdgeTransform]
  ring

/-- Squared rectangular values are absolutely summable as complex terms. -/
theorem xiRectangularTwoEdgeTransform_sq_summable (L a : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2) := by
  apply Summable.of_norm
  simpa only [norm_pow] using!
    (xiRectangularTwoEdgeTransform_squareSummable L a)

/-- The selected dominant-edge series is summable at every fixed aperture. -/
theorem xiRectangularTwoEdgeDominant_summable
    {L a : ℝ} (ha : L ≤ a) :
    Summable (fun q : XiZeroCopy =>
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) := by
  have hsq := xiRectangularTwoEdgeTransform_sq_summable L a
  have hrem := xiRectangularTwoEdgeRemainderTerm_summable ha
  refine (hsq.sub hrem).congr (fun q => ?_)
  rw [xiRectangularTwoEdgeRemainderTerm]
  ring

/-- The difference between the actual rectangular Xi polarization and the
selected dominant-edge sum is exactly the absolutely convergent remainder
series. -/
theorem xiWeilPolarization_rectangular_sub_dominant_eq_tsum_remainder
    {L a : ℝ} (ha : L ≤ a) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a) -
        ∑' q : XiZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q) =
      ∑' q : XiZeroCopy, xiRectangularTwoEdgeRemainderTerm L a q := by
  rw [xiWeilPolarization_rectangular_eq_tsum_sq]
  have hsq := xiRectangularTwoEdgeTransform_sq_summable L a
  have hdom := xiRectangularTwoEdgeDominant_summable ha
  rw [← hsq.tsum_sub hdom]
  apply tsum_congr
  intro q
  rfl

/-- The full multiplicity-exact remainder is bounded by one aperture-independent
constant times the canonical reciprocal-square Xi mass. -/
theorem norm_xiWeilPolarization_rectangular_sub_dominant_le
    {L a : ℝ} (ha : L ≤ a) :
    ‖xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a) -
        ∑' q : XiZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)‖ ≤
      rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [xiWeilPolarization_rectangular_sub_dominant_eq_tsum_remainder ha]
  have hrem := xiRectangularTwoEdgeRemainderTerm_summable ha
  have hmajor := xiSpectralPoint_inv_sq_summable.mul_left
    (rectangularTwoEdgeRemainderBound L)
  calc
    ‖∑' q : XiZeroCopy, xiRectangularTwoEdgeRemainderTerm L a q‖ ≤
        ∑' q : XiZeroCopy, ‖xiRectangularTwoEdgeRemainderTerm L a q‖ :=
      norm_tsum_le_tsum_norm hrem.norm
    _ ≤ ∑' q : XiZeroCopy,
        rectangularTwoEdgeRemainderBound L *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      exact hrem.norm.tsum_le_tsum (fun q => by
        calc
          ‖xiRectangularTwoEdgeRemainderTerm L a q‖ ≤
              rectangularTwoEdgeRemainderBound L / ‖xiSpectralPoint q‖ ^ 2 :=
            norm_xiRectangularTwoEdgeRemainderTerm_le ha q
          _ = rectangularTwoEdgeRemainderBound L *
              (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring) hmajor
    _ = rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [tsum_mul_left]

/-! ## Exact FE--Schwarz quartet identities -/

/-- Conjugating a Xi-divisor copy conjugates its literal centered-zero
coordinate `i z`. -/
theorem I_mul_xiSpectralPoint_copyConj (q : XiZeroCopy) :
    I * xiSpectralPoint (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (I * xiSpectralPoint q) := by
  rw [xiSpectralPoint_copyConj]
  simp only [map_mul, conj_I]
  ring

/-- Functional-equation reflection leaves every rectangular two-edge Xi value
unchanged. -/
theorem xiRectangularTwoEdgeTransform_reflect (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeTransform L a
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) := by
  rw [xiSpectralPoint_reflect, xiRectangularTwoEdgeTransform]
  rw [show I * (-xiSpectralPoint q) = -(I * xiSpectralPoint q) by ring]
  exact rectangularTwoEdgeTransform_even L a (I * xiSpectralPoint q)

/-- Schwarz conjugation of a divisor copy conjugates every rectangular
two-edge Xi value. -/
theorem xiRectangularTwoEdgeTransform_copyConj (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeTransform L a
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      (starRingEnd ℂ)
        (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)) := by
  rw [xiRectangularTwoEdgeTransform, xiRectangularTwoEdgeTransform,
    I_mul_xiSpectralPoint_copyConj]
  exact (rectangularTwoEdgeTransform_conj L a (I * xiSpectralPoint q)).symm

/-- Critical-line reflection also conjugates every rectangular two-edge Xi
value. -/
theorem xiRectangularTwoEdgeTransform_lineConj (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeTransform L a
        (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) =
      (starRingEnd ℂ)
        (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)) := by
  rw [xiZeroCopyLineConjEquiv, Equiv.trans_apply,
    xiRectangularTwoEdgeTransform_reflect,
    xiRectangularTwoEdgeTransform_copyConj]

/-- The four FE--Schwarz copies contribute exactly four times the real part of
one squared rectangular value.  The identity is pointwise and retains analytic
multiplicity because it is stated on `XiZeroCopy`. -/
theorem xiRectangularTwoEdgeTransform_quartet_square (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 +
        xiRectangularTwoEdgeTransform L a
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ^ 2 +
        xiRectangularTwoEdgeTransform L a
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) ^ 2 +
        xiRectangularTwoEdgeTransform L a
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) ^ 2 =
      (((4 * (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2).re : ℝ) : ℂ)) := by
  rw [xiRectangularTwoEdgeTransform_reflect,
    xiRectangularTwoEdgeTransform_copyConj,
    xiRectangularTwoEdgeTransform_lineConj, ← map_pow]
  let y : ℂ := xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2
  change y + y + (starRingEnd ℂ) y + (starRingEnd ℂ) y = ((4 * y.re : ℝ) : ℂ)
  apply Complex.ext
  · simp only [add_re, conj_re, ofReal_re]
    ring
  · simp only [add_im, conj_im, ofReal_im]
    ring

/-- Functional-equation reflection preserves the sign-selected Xi dominant
edge. -/
theorem xiRectangularTwoEdgeDominant_reflect (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeDominant L a
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q) := by
  rw [xiRectangularTwoEdgeDominant, xiRectangularTwoEdgeDominant,
    xiSpectralPoint_reflect]
  rw [show I * (-xiSpectralPoint q) = -(I * xiSpectralPoint q) by ring]
  exact rectangularTwoEdgeDominant_even L a (I * xiSpectralPoint q)

/-- Schwarz conjugation conjugates the sign-selected Xi dominant edge. -/
theorem xiRectangularTwoEdgeDominant_copyConj (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeDominant L a
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      (starRingEnd ℂ)
        (xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) := by
  rw [xiRectangularTwoEdgeDominant, xiRectangularTwoEdgeDominant,
    I_mul_xiSpectralPoint_copyConj]
  exact (rectangularTwoEdgeDominant_conj L a (I * xiSpectralPoint q)).symm

/-- The full multiplicity-exact dominant-edge sum is real. -/
theorem star_tsum_xiRectangularTwoEdgeDominant
    (L a : ℝ) :
    (starRingEnd ℂ) (∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q) := by
  calc
    (starRingEnd ℂ) (∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy,
        (starRingEnd ℂ)
          (xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) := by
        exact Complex.conj_tsum _
    _ = ∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) := by
        apply tsum_congr
        intro q
        exact (xiRectangularTwoEdgeDominant_copyConj L a q).symm
    _ = ∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q) := by
      simpa only using xiZeroCopyConjEquiv.tsum_eq
        (fun q : XiZeroCopy =>
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q))

/-- Therefore the imaginary part of the dominant-edge sum vanishes. -/
theorem tsum_xiRectangularTwoEdgeDominant_im_eq_zero
    (L a : ℝ) :
    (∑' q : XiZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (star_tsum_xiRectangularTwoEdgeDominant L a)

/-! ## A uniform zero-height gap -/

/-- The actual Xi divisor is uniformly separated from the real segment of the
critical strip.  This is qualitative and uses only finiteness of zeros in a
compact disc plus the unconditional absence of real nontrivial Xi zeros. -/
theorem exists_xiDivisorSupport_abs_im_lower_bound :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : XiDivisorSupport, η ≤ |(ρ : ℂ).im| := by
  let Zset : Set ℂ :=
    {z ∈ Metric.closedBall ((1 / 2 : ℝ) : ℂ) 3 | xi z = 0}
  have hZfinite : Zset.Finite := xi_zeros_closedBall_finite ((1 / 2 : ℝ) : ℂ) 3
  let Z : Finset ℂ := hZfinite.toFinset
  let V : Finset ℝ := insert 1 (Z.image fun z => |z.im|)
  have hV : V.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  let η : ℝ := V.min' hV
  have hηmem : η ∈ V := Finset.min'_mem V hV
  have hηpos : 0 < η := by
    rcases Finset.mem_insert.mp hηmem with hηone | hηimage
    · rw [hηone]
      norm_num
    · obtain ⟨z, hzZ, hzη⟩ := Finset.mem_image.mp hηimage
      rw [← hzη]
      apply abs_pos.mpr
      have hzset : z ∈ Zset := by
        exact hZfinite.mem_toFinset.mp hzZ
      have hzsupport : z ∈ (MeromorphicOn.divisor xi Set.univ).support :=
        mem_xi_divisor_support_of_eq_zero hzset.2
      exact xi_divisor_support_im_ne_zero ⟨z, hzsupport⟩
  refine ⟨η, hηpos, fun ρ => ?_⟩
  by_cases hsmall : |(ρ : ℂ).im| < 1
  · have hstrip := xi_divisor_support_re_mem_open_unit ρ
    have hreabs : |((ρ : ℂ) - ((1 / 2 : ℝ) : ℂ)).re| < 1 := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      rw [abs_lt]
      constructor <;> linarith
    have himabs : |((ρ : ℂ) - ((1 / 2 : ℝ) : ℂ)).im| < 1 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hsmall
    have hball : (ρ : ℂ) ∈ Metric.closedBall ((1 / 2 : ℝ) : ℂ) 3 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      apply le_of_lt
      calc
        ‖(ρ : ℂ) - ((1 / 2 : ℝ) : ℂ)‖ ≤
            |((ρ : ℂ) - ((1 / 2 : ℝ) : ℂ)).re| +
              |((ρ : ℂ) - ((1 / 2 : ℝ) : ℂ)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + 1 := add_lt_add hreabs himabs
        _ < 3 := by norm_num
    have hzset : (ρ : ℂ) ∈ Zset :=
      ⟨hball, xi_eq_zero_of_mem_divisor_support ρ⟩
    have hzZ : (ρ : ℂ) ∈ Z := hZfinite.mem_toFinset.mpr hzset
    have himV : |(ρ : ℂ).im| ∈ V := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(ρ : ℂ), hzZ, rfl⟩)
    have hmin : V.min' hV ≤ |(ρ : ℂ).im| := Finset.min'_le V _ himV
    simpa only [η] using hmin
  · have hmin : V.min' hV ≤ 1 :=
      Finset.min'_le V 1 (Finset.mem_insert_self 1 (Z.image fun z => |z.im|))
    have hηone : η ≤ 1 := by simpa only [η] using hmin
    exact hηone.trans (not_lt.mp hsmall)

/-- The same uniform height gap on multiplicity copies. -/
theorem exists_xiZeroCopy_abs_im_lower_bound :
    ∃ η : ℝ, 0 < η ∧ ∀ q : XiZeroCopy, η ≤ |((q.1 : XiDivisorSupport) : ℂ).im| := by
  obtain ⟨η, hη, hbound⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  exact ⟨η, hη, fun q => hbound q.1⟩

end

end RHTower
