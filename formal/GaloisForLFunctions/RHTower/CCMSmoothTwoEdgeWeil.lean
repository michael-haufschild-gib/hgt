import GaloisForLFunctions.RHTower.CCMWeightedXiLandau
import GaloisForLFunctions.RHTower.CCMRectangularDominantFold

/-!
# Smooth fixed-profile two-edge Weil detectors

This module specializes the two-edge Weil decomposition to the literal
smooth fixed-support profile space.  The only analytic input is the
reciprocal-height estimate already proved for the profile Laplace amplitude.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

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
    smoothProfileTwoEdgeTransform f a w ^ 2 =
      smoothProfileLaplaceAmplitude f w ^ 2 *
          Complex.exp (2 * (a : ℂ) * w) +
        2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * w) := by
  have hp : Complex.exp ((a : ℂ) * w) ^ 2 =
      Complex.exp (2 * (a : ℂ) * w) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hn : Complex.exp (-(a : ℂ) * w) ^ 2 =
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
  apply Summable.of_nonneg_of_le
  · intro q
    positivity
  · intro q
    have hz : I * xiSpectralPoint q ≠ 0 :=
      mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
    have h := norm_smoothProfileTwoEdgeTransform_le heta hwindow f a hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
    rw [norm_mul, norm_I, one_mul] at h
    calc
      ‖smoothProfileTwoEdgeTransform f a (I * xiSpectralPoint q)‖ ^ 2 ≤
          (C / ‖xiSpectralPoint q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp
  · exact xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)

/-- Sign-selected growing edge for a smooth profile. -/
def smoothProfileTwoEdgeDominant {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) (a : ℝ) (w : ℂ) : ℂ :=
  if 0 < w.re then
    smoothProfileLaplaceAmplitude f w ^ 2 *
      Complex.exp (2 * (a : ℂ) * w)
  else if w.re < 0 then
    smoothProfileLaplaceAmplitude f (-w) ^ 2 *
      Complex.exp (-2 * (a : ℂ) * w)
  else 0

/-- Aperture-independent reciprocal-square remainder constant. -/
def smoothProfileTwoEdgeRemainderBound {eta L : ℝ}
    (f : SmoothBoundaryProfile eta L) : ℝ :=
  4 * (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ 2

theorem smoothProfileTwoEdgeDominant_logSample_of_pos
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L)
    {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hwre : 0 < w.re) :
    smoothProfileTwoEdgeDominant f (Real.log n / 2) w =
      smoothProfileLaplaceAmplitude f w ^ 2 * (n : ℂ) ^ w := by
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
    smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w =
      2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * w) := by
  rw [smoothProfileTwoEdgeTransform_sq_decomposition,
    smoothProfileTwoEdgeDominant, if_pos hwre]
  ring

theorem smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg
    {eta L a : ℝ} (f : SmoothBoundaryProfile eta L)
    {w : ℂ} (hwre : w.re < 0) :
    smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w =
      2 * smoothProfileLaplaceAmplitude f (-w) *
          smoothProfileLaplaceAmplitude f w +
        smoothProfileLaplaceAmplitude f w ^ 2 *
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
    ‖smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
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
  rw [smoothProfileTwoEdgeTransform_sq_sub_dominant_of_pos f hwre]
  calc
    ‖2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w) +
        smoothProfileLaplaceAmplitude f (-w) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * w)‖ ≤
      ‖2 * smoothProfileLaplaceAmplitude f w *
          smoothProfileLaplaceAmplitude f (-w)‖ +
        ‖smoothProfileLaplaceAmplitude f (-w) ^ 2 *
          Complex.exp (-2 * (a : ℂ) * w)‖ := norm_add_le _ _
    _ ≤ 2 * B * B + B ^ 2 := by
      simp only [norm_mul, norm_ofNat, norm_pow]
      have hAn2 : ‖smoothProfileLaplaceAmplitude f (-w)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hAn 2
      gcongr
    _ ≤ 4 * B ^ 2 := by nlinarith [sq_nonneg B]
    _ = smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
      dsimp only [B, C0, smoothProfileTwoEdgeRemainderBound]
      field_simp

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_of_neg_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    {w : ℂ} (hwre : w.re < 0) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
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
    ‖smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
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
    ‖smoothProfileTwoEdgeTransform f a w‖ ^ 2 ≤ (2 * B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hF 2
    _ = smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
      dsimp only [B, C0, smoothProfileTwoEdgeRemainderBound]
      field_simp
      ring

theorem norm_smoothProfileTwoEdgeTransform_sq_sub_dominant_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    {w : ℂ} (hw : w ≠ 0) (hstrip : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖smoothProfileTwoEdgeTransform f a w ^ 2 -
        smoothProfileTwoEdgeDominant f a w‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖w‖ ^ 2 := by
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
  xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ 2 -
    xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q)

theorem norm_xiSmoothProfileTwoEdgeRemainderTerm_le
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) {a : ℝ} (ha : 0 ≤ a)
    (q : XiZeroCopy) :
    ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ ≤
      smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ 2 := by
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
        smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ 2 :=
      norm_xiSmoothProfileTwoEdgeRemainderTerm_le heta hwindow f ha q
    _ = smoothProfileTwoEdgeRemainderBound f *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem xiWeilPolarization_smoothProfile_eq_tsum_sq
    {eta L : ℝ} (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    xiWeilPolarization (xiSmoothProfileTwoEdgeTransform f a)
        (xiSmoothProfileTwoEdgeTransform f a) =
      ∑' q : XiZeroCopy,
        xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ 2 := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp_xiSmoothProfileTwoEdgeTransform]
  ring

theorem xiSmoothProfileTwoEdgeTransform_sq_summable
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (a : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ 2) := by
  apply Summable.of_norm
  simpa only [norm_pow] using
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
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
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
        (xiSmoothProfileTwoEdgeTransform f a (xiSpectralPoint q) ^ 2 -
          xiSmoothProfileTwoEdgeDominant f a (xiSpectralPoint q))‖ =
      ‖∑' q : XiZeroCopy, xiSmoothProfileTwoEdgeRemainderTerm f a q‖ := by rfl
    _ ≤ ∑' q : XiZeroCopy, ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ :=
      norm_tsum_le_tsum_norm hrem.norm
    _ ≤ ∑' q : XiZeroCopy, smoothProfileTwoEdgeRemainderBound f *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      exact hrem.norm.tsum_le_tsum (fun q => by
        calc
          ‖xiSmoothProfileTwoEdgeRemainderTerm f a q‖ ≤
              smoothProfileTwoEdgeRemainderBound f / ‖xiSpectralPoint q‖ ^ 2 :=
            norm_xiSmoothProfileTwoEdgeRemainderTerm_le heta hwindow f ha q
          _ = smoothProfileTwoEdgeRemainderBound f *
              (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring) hmajor
    _ = smoothProfileTwoEdgeRemainderBound f *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
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
