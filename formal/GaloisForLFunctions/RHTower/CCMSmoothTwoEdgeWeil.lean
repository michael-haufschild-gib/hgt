import GaloisForLFunctions.RHTower.CCMWeightedXiLandau
import GaloisForLFunctions.RHTower.CCMRectangularDominantFold
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Smooth fixed-profile two-edge Weil detectors

This module specializes the two-edge Weil decomposition to the literal
smooth fixed-support profile space.  The only analytic input is the
reciprocal-height estimate already proved for the profile Laplace amplitude.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

open MeasureTheory

/-- Algebraic bilateral transform of the two translates of a smooth boundary
profile. -/
def smoothProfileTwoEdgeTransform {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * smoothProfileLaplaceAmplitude f w +
    Complex.exp (-(a : ℂ) * w) * smoothProfileLaplaceAmplitude f (-w)

theorem smoothProfileTwoEdgeTransform_even {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) :
    smoothProfileTwoEdgeTransform f a (-w) =
      smoothProfileTwoEdgeTransform f a w := by
  rw [smoothProfileTwoEdgeTransform, smoothProfileTwoEdgeTransform]
  simp only [neg_neg]
  ring_nf

theorem smoothProfileTwoEdgeTransform_conj {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (smoothProfileTwoEdgeTransform f a w) =
      smoothProfileTwoEdgeTransform f a ((starRingEnd ℂ) w) := by
  rw [smoothProfileTwoEdgeTransform, smoothProfileTwoEdgeTransform]
  simp only [map_add, map_mul, map_neg, smoothProfileLaplaceAmplitude_conj]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  congr 1 <;> simp

/-- Smooth two-edge transform in the centered Xi spectral coordinate. -/
def xiSmoothProfileTwoEdgeTransform {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (z : ℂ) : ℂ :=
  smoothProfileTwoEdgeTransform f a (I * z)

theorem xiWeilSharp_xiSmoothProfileTwoEdgeTransform {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (z : ℂ) :
    xiWeilSharp (xiSmoothProfileTwoEdgeTransform f a) z =
      xiSmoothProfileTwoEdgeTransform f a z := by
  rw [xiWeilSharp, xiSmoothProfileTwoEdgeTransform,
    smoothProfileTwoEdgeTransform_conj]
  rw [show (starRingEnd ℂ) (I * (starRingEnd ℂ) z) = -(I * z) by simp]
  exact smoothProfileTwoEdgeTransform_even f a (I * z)

/-- Exact three-term square decomposition for an arbitrary smooth profile. -/
theorem smoothProfileTwoEdgeTransform_sq_decomposition {eta L a : ℝ}
    (f : SmoothBoundaryProfile eta L) (w : ℂ) :
    smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) =
      smoothProfileLaplaceAmplitude f w ^ (2 : ℕ) *
          Complex.exp (2 * (a : ℂ) * w) +
        2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ (2 : ℕ) *
          Complex.exp (-2 * (a : ℂ) * w) := by
  have hp : Complex.exp ((a : ℂ) * w) ^ (2 : ℕ) =
      Complex.exp (2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hn : Complex.exp (-(a : ℂ) * w) ^ (2 : ℕ) =
      Complex.exp (-2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hinv : Complex.exp ((a : ℂ) * w) *
      Complex.exp (-(a : ℂ) * w) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [smoothProfileTwoEdgeTransform, add_sq, mul_pow, mul_pow, hp, hn]
  rw [show 2 * (Complex.exp ((a : ℂ) * w) *
      smoothProfileLaplaceAmplitude f w) *
      (Complex.exp (-(a : ℂ) * w) *
        smoothProfileLaplaceAmplitude f (-w)) =
      2 * (Complex.exp ((a : ℂ) * w) *
        Complex.exp (-(a : ℂ) * w)) *
        smoothProfileLaplaceAmplitude f w *
        smoothProfileLaplaceAmplitude f (-w) by ring, hinv]
  ring

private theorem real_mul_re_le_abs_half_profile {c : ℝ} {w : ℂ}
    (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ((c : ℂ) * w).re ≤ |c| / 2 := by
  calc
    ((c : ℂ) * w).re = c * w.re := by simp [Complex.mul_re]
    _ ≤ |c * w.re| := le_abs_self _
    _ = |c| * |w.re| := abs_mul _ _
    _ ≤ |c| * (1 / 2) :=
      mul_le_mul_of_nonneg_left hstrip (abs_nonneg c)
    _ = |c| / 2 := by ring

private theorem norm_exp_real_mul_le_profile {c : ℝ} {w : ℂ}
    (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖Complex.exp ((c : ℂ) * w)‖ ≤ Real.exp (|c| / 2) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (real_mul_re_le_abs_half_profile hstrip)

/-- Reciprocal-height bound for the full smooth two-edge transform at a fixed
aperture. -/
theorem norm_smoothProfileTwoEdgeTransform_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (a : ℝ) {w : ℂ}
    (hw : w ≠ 0) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w‖ ≤
      (2 * Real.exp (|a| / 2) *
        (Real.exp (L / 2) * smoothProfileDerivativeMass f)) / ‖w‖ := by
  let C0 : ℝ := Real.exp (L / 2) * smoothProfileDerivativeMass f
  have hA : ‖smoothProfileLaplaceAmplitude f w‖ ≤ C0 / ‖w‖ :=
    norm_smoothProfileLaplaceAmplitude_le heta hwindow f hw hstrip
  have hAn : ‖smoothProfileLaplaceAmplitude f (-w)‖ ≤ C0 / ‖w‖ := by
    simpa only [norm_neg] using
      norm_smoothProfileLaplaceAmplitude_le heta hwindow f
        (neg_ne_zero.mpr hw) (by simpa using hstrip)
  have hp := norm_exp_real_mul_le_profile (c := a) hstrip
  have hn : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    have h := norm_exp_real_mul_le_profile (c := -a) hstrip
    simpa only [ofReal_neg, abs_neg, neg_mul] using h
  rw [smoothProfileTwoEdgeTransform]
  calc
    ‖Complex.exp ((a : ℂ) * w) * smoothProfileLaplaceAmplitude f w +
        Complex.exp (-(a : ℂ) * w) *
          smoothProfileLaplaceAmplitude f (-w)‖ ≤
      ‖Complex.exp ((a : ℂ) * w) * smoothProfileLaplaceAmplitude f w‖ +
        ‖Complex.exp (-(a : ℂ) * w) *
          smoothProfileLaplaceAmplitude f (-w)‖ := norm_add_le _ _
    _ ≤ Real.exp (|a| / 2) * (C0 / ‖w‖) +
        Real.exp (|a| / 2) * (C0 / ‖w‖) := by
      rw [norm_mul, norm_mul]
      gcongr
    _ = (2 * Real.exp (|a| / 2) * C0) / ‖w‖ := by ring

/-- Every smooth two-edge transform is square-summable on the actual
multiplicity-exact Xi divisor. -/
theorem xiSmoothProfileTwoEdgeTransform_squareSummable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    XiWeilSquareSummable (xiSmoothProfileTwoEdgeTransform f a) := by
  let C : ℝ := 2 * Real.exp (|a| / 2) *
    (Real.exp (L / 2) * smoothProfileDerivativeMass f)
  have hmajor : Summable (fun q : XiZeroCopy =>
      C ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left (C ^ (2 : ℕ))
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) hmajor
  ·
    have hz : I * xiSpectralPoint q ≠ 0 :=
      mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
    have h := norm_smoothProfileTwoEdgeTransform_le heta hwindow f a hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
    rw [norm_mul, norm_I, one_mul] at h
    calc
      ‖smoothProfileTwoEdgeTransform f a (I * xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
          (C / ‖xiSpectralPoint q‖) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by field_simp

/-- Sign-selected growing edge for a smooth profile. -/
def smoothProfileTwoEdgeDominant {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) : ℂ :=
  if 0 < w.re then
    smoothProfileLaplaceAmplitude f w ^ (2 : ℕ) *
      Complex.exp (2 * (a : ℂ) * w)
  else if w.re < 0 then
    smoothProfileLaplaceAmplitude f (-w) ^ (2 : ℕ) *
      Complex.exp (-2 * (a : ℂ) * w)
  else 0

/-- Aperture-independent reciprocal-square remainder constant. -/
def smoothProfileTwoEdgeRemainderBound {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) : ℝ :=
  4 * (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ (2 : ℕ)

theorem smoothProfileTwoEdgeDominant_logSample_of_pos
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L)
    {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hwre : 0 < w.re) :
    smoothProfileTwoEdgeDominant f (Real.log n / 2) w =
      smoothProfileLaplaceAmplitude f w ^ (2 : ℕ) * (n : ℂ) ^ w := by
  rw [smoothProfileTwoEdgeDominant, if_pos hwre]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  congr 1
  push_cast
  ring

theorem smoothProfileTwoEdgeDominant_even {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) :
    smoothProfileTwoEdgeDominant f a (-w) =
      smoothProfileTwoEdgeDominant f a w := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hneg
    rw [smoothProfileTwoEdgeDominant, if_pos hnpos,
      smoothProfileTwoEdgeDominant, if_neg (not_lt.mpr hneg.le), if_pos hneg]
    rw [show 2 * (a : ℂ) * (-w) = -2 * (a : ℂ) * w by ring]
  · have hnzero : (-w).re = 0 := by simpa using congrArg Neg.neg hzero
    rw [smoothProfileTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith),
      smoothProfileTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith)]
  · have hnneg : (-w).re < 0 := by simpa using neg_lt_zero.mpr hpos
    rw [smoothProfileTwoEdgeDominant, if_neg (not_lt.mpr hnneg.le), if_pos hnneg,
      smoothProfileTwoEdgeDominant, if_pos hpos]
    rw [show -2 * (a : ℂ) * (-w) = 2 * (a : ℂ) * w by ring]
    simp only [neg_neg]

theorem smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos
    {eta L a : ℝ} (f : SmoothBoundaryProfile eta L)
    {w : ℂ} (hwre : 0 < w.re) :
    smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w =
      2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ (2 : ℕ) *
          Complex.exp (-2 * (a : ℂ) * w) := by
  rw [smoothProfileTwoEdgeTransform_sq_decomposition,
    smoothProfileTwoEdgeDominant, if_pos hwre]
  ring

theorem smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg
    {eta L a : ℝ} (f : SmoothBoundaryProfile eta L)
    {w : ℂ} (hwre : w.re < 0) :
    smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w =
      2 * smoothProfileLaplaceAmplitude f (-w) *
          smoothProfileLaplaceAmplitude f w +
        smoothProfileLaplaceAmplitude f w ^ (2 : ℕ) *
          Complex.exp (2 * (a : ℂ) * w) := by
  have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hwre
  rw [← smoothProfileTwoEdgeTransform_even f a w,
    ← smoothProfileTwoEdgeDominant_even f a w]
  have h := smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos
    (f := f) (a := a) (w := -w) hnpos
  rw [show -2 * (a : ℂ) * (-w) = 2 * (a : ℂ) * w by ring] at h
  simpa only [neg_neg] using h

@[simp] theorem smoothProfileTwoEdgeDominant_of_re_eq_zero
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ)
    {w : ℂ} (hwre : w.re = 0) :
    smoothProfileTwoEdgeDominant f a w = 0 := by
  rw [smoothProfileTwoEdgeDominant, if_neg (by linarith), if_neg (by linarith)]

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    {w : ℂ} (hwre : 0 < w.re) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
  have hw : w ≠ 0 := by
    intro h
    rw [h] at hwre
    simp at hwre
  let C0 : ℝ := Real.exp (L / 2) * smoothProfileDerivativeMass f
  let B : ℝ := C0 / ‖w‖
  have hC0 : 0 ≤ C0 := mul_nonneg (Real.exp_pos _).le
    (smoothProfileDerivativeMass_nonneg f)
  have hB : 0 ≤ B := div_nonneg hC0 (norm_nonneg _)
  have hA : ‖smoothProfileLaplaceAmplitude f w‖ ≤ B :=
    norm_smoothProfileLaplaceAmplitude_le heta hwindow f hw hstrip
  have hAn : ‖smoothProfileLaplaceAmplitude f (-w)‖ ≤ B := by
    simpa only [norm_neg] using
      norm_smoothProfileLaplaceAmplitude_le heta hwindow f
        (neg_ne_zero.mpr hw) (by simpa using hstrip)
  have hdecRe : (-2 * (a : ℂ) * w).re ≤ 0 := by
    norm_num [Complex.mul_re]
    nlinarith
  have hdec : ‖Complex.exp (-2 * (a : ℂ) * w)‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hdecRe
  have hfirst :
      2 * ‖smoothProfileLaplaceAmplitude f w‖ *
          ‖smoothProfileLaplaceAmplitude f (-w)‖ ≤ 2 * B * B := by
    gcongr
  have hAn2 : ‖smoothProfileLaplaceAmplitude f (-w)‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hAn 2
  have hsecond : ‖smoothProfileLaplaceAmplitude f (-w)‖ ^ (2 : ℕ) *
      ‖Complex.exp (-2 * (a : ℂ) * w)‖ ≤ B ^ (2 : ℕ) := by
    calc
      ‖smoothProfileLaplaceAmplitude f (-w)‖ ^ (2 : ℕ) *
          ‖Complex.exp (-2 * (a : ℂ) * w)‖ ≤ B ^ (2 : ℕ) * 1 :=
        mul_le_mul hAn2 hdec (norm_nonneg _) (sq_nonneg B)
      _ = B ^ (2 : ℕ) := mul_one _
  rw [smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos f hwre]
  calc
    ‖2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ (2 : ℕ) *
          Complex.exp (-2 * (a : ℂ) * w)‖ ≤
      ‖2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w)‖ +
        ‖smoothProfileLaplaceAmplitude f (-w) ^ (2 : ℕ) *
          Complex.exp (-2 * (a : ℂ) * w)‖ := norm_add_le _ _
    _ ≤ 2 * B * B + B ^ (2 : ℕ) := by
      simp only [norm_mul, norm_ofNat, norm_pow]
      exact add_le_add hfirst hsecond
    _ ≤ 4 * B ^ (2 : ℕ) := by nlinarith [sq_nonneg B]
    _ = smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
      dsimp only [B, C0, smoothProfileTwoEdgeRemainderBound]
      field_simp

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    {w : ℂ} (hwre : w.re < 0) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
  have hnpos : 0 < (-w).re := by simpa using neg_pos.mpr hwre
  have hnstrip : |(-w).re| ≤ (1 / 2 : ℝ) := by simpa using hstrip
  have h := norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos_le
    heta hwindow f ha hnpos hnstrip
  rw [smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos f hnpos] at h
  rw [show -2 * (a : ℂ) * (-w) = 2 * (a : ℂ) * w by ring] at h
  rw [smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg f hwre]
  simpa only [norm_neg, neg_neg] using h

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_re_eq_zero_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (a : ℝ)
    {w : ℂ} (hw : w ≠ 0) (hwre : w.re = 0) :
    ‖smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
  let C0 : ℝ := Real.exp (L / 2) * smoothProfileDerivativeMass f
  let B : ℝ := C0 / ‖w‖
  have hC0 : 0 ≤ C0 := mul_nonneg (Real.exp_pos _).le
    (smoothProfileDerivativeMass_nonneg f)
  have hB : 0 ≤ B := div_nonneg hC0 (norm_nonneg _)
  have hstrip : |w.re| ≤ (1 / 2 : ℝ) := by rw [hwre]; norm_num
  have hA : ‖smoothProfileLaplaceAmplitude f w‖ ≤ B :=
    norm_smoothProfileLaplaceAmplitude_le heta hwindow f hw hstrip
  have hAn : ‖smoothProfileLaplaceAmplitude f (-w)‖ ≤ B := by
    simpa only [norm_neg] using
      norm_smoothProfileLaplaceAmplitude_le heta hwindow f
        (neg_ne_zero.mpr hw) (by simpa using hstrip)
  have hp : ‖Complex.exp ((a : ℂ) * w)‖ = 1 := by
    rw [Complex.norm_exp, show ((a : ℂ) * w).re = 0 by
      simp [Complex.mul_re, hwre], Real.exp_zero]
  have hn : ‖Complex.exp (-(a : ℂ) * w)‖ = 1 := by
    rw [Complex.norm_exp, show (-(a : ℂ) * w).re = 0 by
      simp [Complex.mul_re, hwre], Real.exp_zero]
  have hF : ‖smoothProfileTwoEdgeTransform f a w‖ ≤ 2 * B := by
    rw [smoothProfileTwoEdgeTransform]
    calc
      ‖Complex.exp ((a : ℂ) * w) * smoothProfileLaplaceAmplitude f w +
          Complex.exp (-(a : ℂ) * w) *
            smoothProfileLaplaceAmplitude f (-w)‖ ≤
        ‖Complex.exp ((a : ℂ) * w) * smoothProfileLaplaceAmplitude f w‖ +
          ‖Complex.exp (-(a : ℂ) * w) *
            smoothProfileLaplaceAmplitude f (-w)‖ := norm_add_le _ _
      _ ≤ B + B := by
        rw [norm_mul, norm_mul, hp, hn, one_mul, one_mul]
        gcongr
      _ = 2 * B := by ring
  rw [smoothProfileTwoEdgeDominant_of_re_eq_zero f a hwre, sub_zero, norm_pow]
  calc
    ‖smoothProfileTwoEdgeTransform f a w‖ ^ (2 : ℕ) ≤ (2 * B) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hF 2
    _ = smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
      dsimp only [B, C0, smoothProfileTwoEdgeRemainderBound]
      field_simp
      ring

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    {w : ℂ} (hw : w ≠ 0) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w ^ (2 : ℕ) -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ (2 : ℕ) := by
  rcases lt_trichotomy w.re 0 with hneg | hzero | hpos
  · exact norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg_le
      heta hwindow f ha hneg hstrip
  · exact norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_re_eq_zero_le
      heta hwindow f a hw hzero
  · exact norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos_le
      heta hwindow f ha hpos hstrip

/-- Dominant edge in the centered Xi spectral coordinate. -/
def xiSmoothProfileTwoEdgeDominant {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (z : ℂ) : ℂ :=
  smoothProfileTwoEdgeDominant f a (I * z)

/-- Multiplicity-exact smooth-profile remainder term. -/
def xiSmoothProfileTwoEdgeRemainderTerm {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (q : XiZeroCopy) : ℂ :=
  xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ (2 : ℕ) -
    xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)

theorem norm_xiSmoothProfileTwoEdgeRemainderTerm_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    (q : XiZeroCopy) :
    ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  have h := norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_le
    heta hwindow f ha hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
  rw [norm_mul, norm_I, one_mul] at h
  simpa only [xiSmoothProfileTwoEdgeRemainderTerm,
    xiSmoothProfileTwoEdgeTransform, xiSmoothProfileTwoEdgeDominant] using h

theorem xiSmoothProfileTwoEdgeRemainderTerm_summable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a) :
    Summable (xiSmoothProfileTwoEdgeRemainderTerm f a) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      (smoothProfileTwoEdgeRemainderBound f))
  intro q
  calc
    ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ ≤
        smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
      norm_xiSmoothProfileTwoEdgeRemainderTerm_le heta hwindow f ha q
    _ = smoothProfileTwoEdgeRemainderBound f *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

theorem xiWeilPolarization_smoothProfile_eq_tsum_sq
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    xiWeilPolarization (xiSmoothProfileTwoEdgeTransform f a)
        (xiSmoothProfileTwoEdgeTransform f a) =
      ∑' q : XiZeroCopy,
        xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ (2 : ℕ) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp_xiSmoothProfileTwoEdgeTransform]
  ring

theorem xiSmoothProfileTwoEdgeTransform_sq_summable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ (2 : ℕ)) := by
  apply Summable.of_norm
  simpa only [XiWeilSquareSummable, norm_pow] using
    xiSmoothProfileTwoEdgeTransform_squareSummable heta hwindow f a

theorem xiSmoothProfileTwoEdgeDominant_summable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun q : XiZeroCopy =>
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)) := by
  have hsq := xiSmoothProfileTwoEdgeTransform_sq_summable
    heta hwindow f a
  have hrem := xiSmoothProfileTwoEdgeRemainderTerm_summable
    heta hwindow f ha
  refine (hsq.sub hrem).congr (fun q => ?_)
  rw [xiSmoothProfileTwoEdgeRemainderTerm]
  ring

theorem norm_xiWeilPolarization_smoothProfile_sub_dominant_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a) :
    ‖xiWeilPolarization (xiSmoothProfileTwoEdgeTransform f a)
          (xiSmoothProfileTwoEdgeTransform f a) -
        ∑' q : XiZeroCopy,
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)‖ ≤
      smoothProfileTwoEdgeRemainderBound f *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [xiWeilPolarization_smoothProfile_eq_tsum_sq]
  have hsq := xiSmoothProfileTwoEdgeTransform_sq_summable
    heta hwindow f a
  have hdom := xiSmoothProfileTwoEdgeDominant_summable
    heta hwindow f ha
  rw [← hsq.tsum_sub hdom]
  have hrem := xiSmoothProfileTwoEdgeRemainderTerm_summable
    heta hwindow f ha
  have hmajor := xiSpectralPoint_inv_sq_summable.mul_left
    (smoothProfileTwoEdgeRemainderBound f)
  calc
    ‖∑' q : XiZeroCopy,
        (xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ (2 : ℕ) -
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q))‖ =
      ‖∑' q : XiZeroCopy, xiSmoothProfileTwoEdgeRemainderTerm f a q‖ := by rfl
    _ ≤ ∑' q : XiZeroCopy, ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ :=
      norm_tsum_le_tsum_norm hrem.norm
    _ ≤ ∑' q : XiZeroCopy, smoothProfileTwoEdgeRemainderBound f *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      exact hrem.norm.tsum_le_tsum (fun q => by
        calc
          ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ ≤
              smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
            norm_xiSmoothProfileTwoEdgeRemainderTerm_le heta hwindow f ha q
          _ = smoothProfileTwoEdgeRemainderBound f *
              (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring) hmajor
    _ = smoothProfileTwoEdgeRemainderBound f *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      rw [tsum_mul_left]

theorem xiSmoothProfileTwoEdgeDominant_reflect
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ)
    (q : XiZeroCopy) :
    xiSmoothProfileTwoEdgeDominant f a
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q) := by
  rw [xiSmoothProfileTwoEdgeDominant, xiSmoothProfileTwoEdgeDominant,
    xiSpectralPoint_reflect]
  rw [mul_neg]
  exact smoothProfileTwoEdgeDominant_even f a (I * xiSpectralPoint q)

end

end RHTower

namespace RHTower

noncomputable section

/-- The reflected left smooth dominant sum equals the right dominant sum. -/
theorem tsum_xiSmoothProfileTwoEdgeDominant_left_eq_right
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    (∑' q : XiLeftZeroCopy,
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1)) =
    ∑' q : XiRightZeroCopy,
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := by
  calc
    (∑' q : XiLeftZeroCopy,
        xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1)) =
      ∑' q : XiRightZeroCopy,
        xiSmoothProfileTwoEdgeDominant f a
          (xiSpectralPoint (xiRightLeftReflectEquiv q).1) :=
      (xiRightLeftReflectEquiv.tsum_eq
        (fun q : XiLeftZeroCopy =>
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1))).symm
    _ = ∑' q : XiRightZeroCopy,
        xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := by
      apply tsum_congr
      intro q
      exact xiSmoothProfileTwoEdgeDominant_reflect f a q.1

/-- The full smooth dominant Xi series folds exactly to twice the
positive-transverse half. -/
theorem tsum_xiSmoothProfileTwoEdgeDominant_eq_two_mul_right
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a) :
    (∑' q : XiZeroCopy,
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)) =
    2 * ∑' q : XiRightZeroCopy,
      xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := by
  let g : XiZeroCopy → ℂ := fun q =>
    xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)
  let P : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  let M : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  have hsum : Summable g :=
    xiSmoothProfileTwoEdgeDominant_summable heta hwindow f ha
  have hpoint : g = P.indicator g + M.indicator g := by
    funext q
    rcases lt_trichotomy (I * xiSpectralPoint q).re 0 with hneg | hzero | hpos
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem]
      · simp only [zero_add]
      · exact hneg
      · exact not_lt.mpr hneg.le
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_notMem,
        add_zero]
      · dsimp only [g, xiSmoothProfileTwoEdgeDominant]
        rw [smoothProfileTwoEdgeDominant, if_neg (by linarith),
          if_neg (by linarith)]
      · change ¬(I * xiSpectralPoint q).re < 0
        linarith
      · change ¬0 < (I * xiSpectralPoint q).re
        linarith
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem,
        add_zero]
      · exact not_lt.mpr hpos.le
      · exact hpos
  calc
    (∑' q : XiZeroCopy,
        xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy, g q := rfl
    _ = ∑' q : XiZeroCopy, (P.indicator g q + M.indicator g q) := by
      apply tsum_congr
      intro q
      exact congrFun hpoint q
    _ = (∑' q : XiZeroCopy, P.indicator g q) +
        ∑' q : XiZeroCopy, M.indicator g q :=
      (hsum.indicator P).tsum_add (hsum.indicator M)
    _ = (∑' q : P, g q.1) + ∑' q : M, g q.1 := by
      rw [tsum_subtype, tsum_subtype]
    _ = (∑' q : XiRightZeroCopy,
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1)) +
        ∑' q : XiLeftZeroCopy,
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := rfl
    _ = (∑' q : XiRightZeroCopy,
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1)) +
        ∑' q : XiRightZeroCopy,
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := by
      rw [tsum_xiSmoothProfileTwoEdgeDominant_left_eq_right]
    _ = 2 * ∑' q : XiRightZeroCopy,
        xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q.1) := by ring

/-- At logarithmic aperture a right smooth dominant edge is the coefficient
of the generic weighted Landau carrier times its Dirichlet monomial. -/
theorem xiSmoothProfileTwoEdgeDominant_logSample_of_right
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    {n : ℕ} (hn : 1 ≤ n) (q : XiRightZeroCopy) :
    xiSmoothProfileTwoEdgeDominant f (Real.log n / 2)
        (xiSpectralPoint q.1) =
      (smoothProfileXiRightCoefficientSystem heta hwindow f hf).coefficient q *
        (n : ℂ) ^ xiRightCenteredZero q := by
  simpa only [xiSmoothProfileTwoEdgeDominant, xiRightCenteredZero,
    smoothProfileXiRightCoefficientSystem] using
    smoothProfileTwoEdgeDominant_logSample_of_pos f hn q.2

/-- The full logarithmic dominant carrier is exactly the real weighted
right-divisor Dirichlet coefficient. -/
theorem tsum_xiSmoothProfileTwoEdgeDominant_logSample_eq_ofReal_weighted
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : XiZeroCopy,
      xiSmoothProfileTwoEdgeDominant f (Real.log n / 2)
        (xiSpectralPoint q)) =
      (xiWeightedRightDirichletCoefficientReal
        (smoothProfileXiRightCoefficientSystem heta hwindow f hf) n : ℂ) := by
  let D := smoothProfileXiRightCoefficientSystem heta hwindow f hf
  have ha : 0 ≤ Real.log n / 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  rw [tsum_xiSmoothProfileTwoEdgeDominant_eq_two_mul_right
    heta hwindow f ha]
  rw [ofReal_xiWeightedRightDirichletCoefficientReal, xiWeightedRightDirichletComplex]
  congr 1
  apply tsum_congr
  intro q
  rw [xiWeightedRightDirichletTerm]
  exact xiSmoothProfileTwoEdgeDominant_logSample_of_right
    heta hwindow f hf hn q

/-- Every generic fixed smooth profile has Weil values below every real level
at arbitrarily late physical apertures when the right Xi divisor is nonempty. -/
theorem xiWeilPolarization_smoothProfile_logSample_cofinally_unbounded_below
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L)
    (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L < Real.log n / 2 ∧
      (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re < B := by
  intro B N0
  let D := smoothProfileXiRightCoefficientSystem heta hwindow f hf
  let K : ℝ := smoothProfileTwoEdgeRemainderBound f *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max (N0 : ℝ) (Real.exp (2 * L)))
  have hN0 : N0 ≤ N := by
    exact_mod_cast (le_max_left (N0 : ℝ) (Real.exp (2 * L))).trans hN.le
  have hNexp : Real.exp (2 * L) < (N : ℝ) :=
    (le_max_right (N0 : ℝ) (Real.exp (2 * L))).trans_lt hN
  obtain ⟨n, hnN, hcoeff⟩ :=
    xiWeightedRightDirichletCoefficientReal_cofinally_unbounded_below
      D hne (B - K) N
  have hn0 : N0 ≤ n := hN0.trans hnN
  have hnexp : Real.exp (2 * L) < (n : ℝ) := by
    exact hNexp.trans_le (by exact_mod_cast hnN)
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hnexp
  have hnNatPos : 0 < n := by exact_mod_cast hnpos
  have hn1 : 1 ≤ n := hnNatPos
  have hlog : 2 * L < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  have hLa : L < Real.log n / 2 := by linarith
  have ha : 0 ≤ Real.log n / 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  refine ⟨n, hn0, hLa, ?_⟩
  have hrem := norm_xiWeilPolarization_smoothProfile_sub_dominant_le
    heta hwindow f ha
  rw [tsum_xiSmoothProfileTwoEdgeDominant_logSample_eq_ofReal_weighted
    heta hwindow f hf hn1] at hrem
  have hre := Complex.re_le_norm
    (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2)) -
      (xiWeightedRightDirichletCoefficientReal D n : ℂ))
  change
    (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re -
      xiWeightedRightDirichletCoefficientReal D n ≤
      ‖xiWeilPolarization
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2)) -
        (xiWeightedRightDirichletCoefficientReal D n : ℂ)‖ at hre
  dsimp only [K] at hcoeff ⊢
  linarith

/-- False RH forces cofinal negative divergence for every profile in the
residual simultaneous-nonvanishing set. -/
theorem not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (hRH : ¬RiemannHypothesis)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L < Real.log n / 2 ∧
      (xiWeilPolarization
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
        (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re < B := by
  exact xiWeilPolarization_smoothProfile_logSample_cofinally_unbounded_below
    heta hwindow f hf (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)

/-- Pointwise Weil positivity on the literal fixed-support smooth two-edge
family is exactly RH. -/
theorem riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta) :
    RiemannHypothesis ↔
      ∀ (f : SmoothBoundaryProfile eta L) (n : ℕ),
        L < Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re := by
  constructor
  · intro hRH f n hn
    exact (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
      (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
      (xiSmoothProfileTwoEdgeTransform_squareSummable
        heta hwindow f (Real.log n / 2))
  · intro hnonneg
    by_contra hRH
    obtain ⟨f, hf⟩ : (xiSmoothProfileGenericSet eta L).Nonempty :=
      (xiSmoothProfileGenericSet_dense_residual hwindow).1.nonempty
    obtain ⟨n, hn0, hLa, hneg⟩ :=
      not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below
        heta hwindow hRH f hf 0 0
    exact (not_lt_of_ge (hnonneg f n hLa)) hneg

/-- Mere eventual lower boundedness of every smooth two-edge profile is also
exactly RH; false RH supplies a residual family violating it. -/
theorem riemannHypothesis_iff_smoothProfile_logSample_weil_eventually_bddBelow
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta) :
    RiemannHypothesis ↔
      ∀ f : SmoothBoundaryProfile eta L,
        ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
          L < Real.log n / 2 →
          B ≤ (xiWeilPolarization
            (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
            (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re := by
  constructor
  · intro hRH f
    refine ⟨0, 0, ?_⟩
    intro n hn hLa
    exact (riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg
      heta hwindow).mp hRH f n hLa
  · intro hlower
    by_contra hRH
    obtain ⟨f, hf⟩ : (xiSmoothProfileGenericSet eta L).Nonempty :=
      (xiSmoothProfileGenericSet_dense_residual hwindow).1.nonempty
    obtain ⟨B, N0, hB⟩ := hlower f
    obtain ⟨n, hn, hLa, hbelow⟩ :=
      not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below
        heta hwindow hRH f hf B N0
    exact (not_lt_of_ge (hB n hn hLa)) hbelow

/-- Every single profile in the residual simultaneous-nonvanishing set is itself a complete
fixed-width RH detector on the logarithmic mesh. -/
theorem riemannHypothesis_iff_generic_smoothProfile_logSample_weil_nonneg
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L) :
    RiemannHypothesis ↔
      ∀ n : ℕ, L < Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re := by
  constructor
  · intro hRH n hn
    exact (riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg
      heta hwindow).mp hRH f n hn
  · intro hnonneg
    by_contra hRH
    obtain ⟨n, _hn0, hLa, hneg⟩ :=
      not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below
        heta hwindow hRH f hf 0 0
    exact (not_lt_of_ge (hnonneg n hLa)) hneg

/-- Every single generic smooth profile also detects RH through mere eventual lower
boundedness; under false RH its samples are cofinally below every real level. -/
theorem riemannHypothesis_iff_generic_smoothProfile_logSample_weil_eventually_bddBelow
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        L < Real.log n / 2 →
        B ≤ (xiWeilPolarization
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))
          (xiSmoothProfileTwoEdgeTransform f (Real.log n / 2))).re := by
  constructor
  · intro hRH
    refine ⟨0, 0, ?_⟩
    intro n _hn hLa
    exact (riemannHypothesis_iff_generic_smoothProfile_logSample_weil_nonneg
      heta hwindow f hf).mp hRH n hLa
  · rintro ⟨B, N0, hB⟩
    by_contra hRH
    obtain ⟨n, hn, hLa, hbelow⟩ :=
      not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below
        heta hwindow hRH f hf B N0
    exact (not_lt_of_ge (hB n hn hLa)) hbelow

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory

/-- The literal pair of translated smooth boundary profiles.  Under the
physical separation condition `L<a`, this is exactly `x ↦ f (a-|x|)`. -/
def smoothProfileTwoEdgePhysical {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a x : ℝ) : ℝ :=
  f (a - x) + f (a + x)

private theorem smoothProfile_eq_zero_of_not_mem_support
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) {x : ℝ}
    (hx : x ∉ Icc eta (L - eta)) : f x = 0 := by
  by_contra hne
  have hs : x ∈ support (fun y : ℝ => f y) := hne
  have ht : x ∈ tsupport (fun y : ℝ => f y) := subset_tsupport _ hs
  exact hx (f.tsupport_subset ht)

/-- The translated-pair realization is the card's literal
`f (a - |x|)` profile once the two supports are separated. -/
theorem smoothProfileTwoEdgePhysical_eq_abs
    {eta L : ℝ} (heta : 0 < eta) (f : SmoothBoundaryProfile eta L)
    {a : ℝ} (ha : L < a) (x : ℝ) :
    smoothProfileTwoEdgePhysical f a x = f (a - |x|) := by
  by_cases hx : 0 ≤ x
  · have hzero : f (a + x) = 0 := by
      apply smoothProfile_eq_zero_of_not_mem_support f
      intro hmem
      have := hmem.2
      linarith
    rw [smoothProfileTwoEdgePhysical, abs_of_nonneg hx, hzero, add_zero]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hzero : f (a - x) = 0 := by
      apply smoothProfile_eq_zero_of_not_mem_support f
      intro hmem
      have := hmem.2
      linarith
    rw [smoothProfileTwoEdgePhysical, abs_of_neg hx', hzero, zero_add]
    congr 1
    ring

private theorem integrable_smoothProfileLaplaceBase
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (w : ℂ) :
    Integrable (fun x : ℝ =>
      (f x : ℂ) * smoothProfileLaplaceWeight w x) := by
  have hf : Continuous (fun x : ℝ => (f x : ℂ)) :=
    Complex.continuous_ofReal.comp f.contDiff.continuous
  have hsupp : HasCompactSupport (fun x : ℝ =>
      (f x : ℂ) * smoothProfileLaplaceWeight w x) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    have hzero := smoothProfile_eq_zero_of_not_mem_support f hx
    simp [hzero]
  exact (hf.mul (continuous_smoothProfileLaplaceWeight w)).integrable_of_hasCompactSupport
    hsupp

/-- Exact bilateral Laplace integral of the literal smooth two-edge profile. -/
theorem integral_smoothProfileTwoEdgePhysical_mul_exp_eq_transform
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) :
    (∫ x : ℝ, (smoothProfileTwoEdgePhysical f a x : ℂ) *
      Complex.exp (w * x)) = smoothProfileTwoEdgeTransform f a w := by
  let gm : ℝ → ℂ := fun s =>
    (f s : ℂ) * smoothProfileLaplaceWeight w s
  let gp : ℝ → ℂ := fun s =>
    (f s : ℂ) * smoothProfileLaplaceWeight (-w) s
  have hgm : Integrable gm := integrable_smoothProfileLaplaceBase f w
  have hgp : Integrable gp := integrable_smoothProfileLaplaceBase f (-w)
  have hrightPoint : (fun x : ℝ =>
      (f (a - x) : ℂ) * Complex.exp (w * x)) =
      fun x => Complex.exp ((a : ℂ) * w) * gm (a - x) := by
    funext x
    dsimp only [gm, smoothProfileLaplaceWeight]
    have he : Complex.exp (w * x) =
        Complex.exp ((a : ℂ) * w) *
          Complex.exp (-(a - x : ℝ) * w) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hleftPoint : (fun x : ℝ =>
      (f (a + x) : ℂ) * Complex.exp (w * x)) =
      fun x => Complex.exp (-(a : ℂ) * w) * gp (a + x) := by
    funext x
    dsimp only [gp, smoothProfileLaplaceWeight]
    have he : Complex.exp (w * x) =
        Complex.exp (-(a : ℂ) * w) *
          Complex.exp (-(a + x : ℝ) * (-w)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hgmSub : Integrable (fun x : ℝ => gm (a - x)) := by
    simpa only [sub_eq_add_neg] using (hgm.comp_add_left a).comp_neg
  have hgpAdd : Integrable (fun x : ℝ => gp (a + x)) := hgp.comp_add_left a
  have hright : Integrable (fun x : ℝ =>
      (f (a - x) : ℂ) * Complex.exp (w * x)) := by
    rw [hrightPoint]
    exact hgmSub.const_mul _
  have hleft : Integrable (fun x : ℝ =>
      (f (a + x) : ℂ) * Complex.exp (w * x)) := by
    rw [hleftPoint]
    exact hgpAdd.const_mul _
  have hgmSubIntegral : (∫ x : ℝ, gm (a - x)) = ∫ x : ℝ, gm x := by
    calc
      (∫ x : ℝ, gm (a - x)) = ∫ x : ℝ, (fun y => gm (a + y)) (-x) := by
        simp only [sub_eq_add_neg]
      _ = ∫ x : ℝ, gm (a + x) :=
        integral_neg_eq_self (fun x : ℝ => gm (a + x)) volume
      _ = ∫ x : ℝ, gm x := integral_add_left_eq_self gm a
  have hgpAddIntegral : (∫ x : ℝ, gp (a + x)) = ∫ x : ℝ, gp x :=
    integral_add_left_eq_self gp a
  rw [show (fun x : ℝ => (smoothProfileTwoEdgePhysical f a x : ℂ) *
      Complex.exp (w * x)) =
      (fun x : ℝ => (f (a - x) : ℂ) * Complex.exp (w * x)) +
      (fun x : ℝ => (f (a + x) : ℂ) * Complex.exp (w * x)) by
    funext x
    simp only [smoothProfileTwoEdgePhysical, Pi.add_apply]
    push_cast
    ring]
  change (∫ x : ℝ,
      (f (a - x) : ℂ) * Complex.exp (w * x) +
        (f (a + x) : ℂ) * Complex.exp (w * x)) = _
  rw [integral_add hright hleft, hrightPoint, hleftPoint,
    integral_const_mul, integral_const_mul, hgmSubIntegral, hgpAddIntegral]
  rw [← smoothProfileLaplaceAmplitude_eq_integral f w,
    ← smoothProfileLaplaceAmplitude_eq_integral f (-w)]
  rfl

/-- Exact transform formula for the card's literal `f(a-|x|)` profile. -/
theorem integral_smoothProfile_abs_twoEdge_mul_exp_eq_transform
    {eta L : ℝ} (heta : 0 < eta) (f : SmoothBoundaryProfile eta L)
    {a : ℝ} (ha : L < a) (w : ℂ) :
    (∫ x : ℝ, (f (a - |x|) : ℂ) * Complex.exp (w * x)) =
      smoothProfileTwoEdgeTransform f a w := by
  rw [← integral_smoothProfileTwoEdgePhysical_mul_exp_eq_transform f a w]
  apply integral_congr_ae
  filter_upwards with x
  rw [smoothProfileTwoEdgePhysical_eq_abs heta f ha x]

end

end RHTower
