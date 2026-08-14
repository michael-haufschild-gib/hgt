import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualNegativeContour

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

def smoothAFEZetaChiShiftQuarterHeightDerivative (tau v : ℝ) : ℂ :=
  I * smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) *
    (logDeriv zetaChi
        (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (linePt tau))

def smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative
    (tau v : ℝ) : ℂ :=
  2 * smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) *
    smoothAFEZetaChiShiftQuarterHeightDerivative tau v

theorem hasDerivAt_smoothAFEZetaChiShiftRatio_quarter
    (tau v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
        (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))
      (smoothAFEZetaChiShiftQuarterHeightDerivative tau v) tau := by
  let w : ℂ := -(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hnumA : Gammaℝ (1 - (linePt tau + w)) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    dsimp only [w]
    simp [linePt]
    norm_num
  have hnum0 : zetaChi (linePt tau + w) ≠ 0 := by
    unfold zetaChi
    apply div_ne_zero
    · apply Gammaℝ_ne_zero_of_re_pos
      dsimp only [w]
      simp [linePt]
      norm_num
    · apply Gammaℝ_ne_zero_of_re_pos
      dsimp only [w]
      simp [linePt]
      norm_num
  have h := hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv hnumA hnum0
  simpa [w, smoothAFEZetaChiShiftQuarterHeightDerivative, sub_eq_add_neg] using h

theorem hasDerivAt_smoothAFEZetaChiShiftRatioSq_quarter
    (tau v : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2)
      (smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v) tau := by
  have hp := (hasDerivAt_smoothAFEZetaChiShiftRatio_quarter tau v).pow 2
  change HasDerivAt
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2) _ tau at hp
  change HasDerivAt
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2)
      (smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v) tau
  simpa [smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative] using hp

theorem norm_digamma_positive_conductor_increment_quarter_le
    {tau v a : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau)
    (haLow : 1 / 8 ≤ a) (haHigh : a ≤ 3 / 8) :
    ‖Complex.digamma
        ((a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) -
      Complex.digamma
        (((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let z0 : ℂ := ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I
  let z1 : ℂ := (a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I
  have htau0 : 0 < tau := by linarith
  have hline : ∀ r : ℝ, AffineMap.lineMap z0 z1 r =
      (((1 / 4 : ℝ) + r * (a - 1 / 4) : ℝ) : ℂ) +
        (((tau - r * v) / 2 : ℝ) : ℂ) * I := by
    intro r
    apply Complex.ext <;> simp [z0, z1, AffineMap.lineMap_apply] <;> ring
  have hdiff : ∀ z ∈ segment ℝ z0 z1,
      DifferentiableAt ℂ Complex.digamma z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    apply (digamma_analyticOnNhd_re_pos _ ?_).differentiableAt
    rw [hline]
    change 0 <
      ((((1 / 4 : ℝ) + r * (a - 1 / 4) : ℝ) : ℂ) +
        (((tau - r * v) / 2 : ℝ) : ℂ) * I).re
    norm_num
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    by_cases ha : 1 / 4 ≤ a
    · nlinarith
    · have hrewrite : (1 / 4 : ℝ) + r * (a - 1 / 4) =
          (1 - r) * (1 / 4) + r * a := by ring
      rw [hrewrite]
      have h1r : 0 ≤ 1 - r := by linarith
      have hconv : (1 / 8 : ℝ) ≤
          (1 - r) * (1 / 4) + r * a := by
        calc
          (1 / 8 : ℝ) = (1 - r) * (1 / 8) + r * (1 / 8) := by ring
          _ ≤ (1 - r) * (1 / 4) + r * a :=
            add_le_add
              (mul_le_mul_of_nonneg_left (by norm_num) h1r)
              (mul_le_mul_of_nonneg_left haLow hr0)
      linarith
  have hbound : ∀ z ∈ segment ℝ z0 z1,
      ‖deriv Complex.digamma z‖ ≤
        16 / tau ^ 2 + 2 * Real.pi / tau := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hrv : r * v ≤ |v| := by
      calc
        r * v ≤ r * |v| := mul_le_mul_of_nonneg_left (le_abs_self v) hr0
        _ ≤ 1 * |v| := mul_le_mul_of_nonneg_right hr1 (abs_nonneg v)
        _ = |v| := one_mul _
    have ht : tau / 4 ≤ (tau - r * v) / 2 := by linarith
    have htpos : 0 < (tau - r * v) / 2 :=
      lt_of_lt_of_le (by positivity) ht
    have hsigma : 0 < (1 / 4 : ℝ) + r * (a - 1 / 4) := by
      by_cases ha : 1 / 4 ≤ a
      · nlinarith
      · have hrewrite : (1 / 4 : ℝ) + r * (a - 1 / 4) =
            (1 - r) * (1 / 4) + r * a := by ring
        rw [hrewrite]
        nlinarith
    rw [hline]
    refine (norm_deriv_digamma_vertical_le hsigma htpos).trans ?_
    have htau4 : 0 < tau / 4 := by positivity
    have hsquare : 1 / ((tau - r * v) / 2) ^ 2 ≤
        16 / tau ^ 2 := by
      have hsq : (tau / 4) ^ 2 ≤ ((tau - r * v) / 2) ^ 2 :=
        (sq_le_sq₀ htau4.le htpos.le).2 ht
      have hi := one_div_le_one_div_of_le (sq_pos_of_pos htau4) hsq
      have heq : 1 / (tau / 4) ^ 2 = 16 / tau ^ 2 := by
        field_simp
        norm_num
      exact hi.trans_eq heq
    have hpi : Real.pi / (2 * ((tau - r * v) / 2)) ≤
        2 * Real.pi / tau := by
      have hden : 2 * (tau / 4) ≤
          2 * ((tau - r * v) / 2) := by nlinarith
      have hi := one_div_le_one_div_of_le
        (by positivity : 0 < 2 * (tau / 4)) hden
      have hmul := mul_le_mul_of_nonneg_left hi Real.pi_pos.le
      calc
        Real.pi / (2 * ((tau - r * v) / 2)) =
            Real.pi * (1 / (2 * ((tau - r * v) / 2))) := by ring
        _ ≤ Real.pi * (1 / (2 * (tau / 4))) := hmul
        _ = 2 * Real.pi / tau := by field_simp; norm_num
    linarith
  have hmvt := (convex_segment z0 z1).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (left_mem_segment ℝ z0 z1) (right_mem_segment ℝ z0 z1)
  have haDiff : |a - 1 / 4| ≤ 1 / 8 := by
    rw [abs_le]
    constructor <;> linarith
  have hnorm : ‖z1 - z0‖ ≤ 1 + |v| := by
    have hrepr : z1 - z0 =
        ((a - 1 / 4 : ℝ) : ℂ) + (((-v / 2 : ℝ) : ℂ) * I) := by
      dsimp only [z0, z1]
      push_cast
      ring
    rw [hrepr]
    calc
      ‖((a - 1 / 4 : ℝ) : ℂ) + (((-v / 2 : ℝ) : ℂ) * I)‖ ≤
          ‖((a - 1 / 4 : ℝ) : ℂ)‖ +
            ‖(((-v / 2 : ℝ) : ℂ) * I)‖ := norm_add_le _ _
      _ = |a - 1 / 4| + |v| / 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I,
          mul_one]
        rw [abs_div, abs_neg]
        norm_num
      _ ≤ 1 + |v| := by linarith [abs_nonneg v]
  dsimp only [z0, z1] at hmvt
  exact hmvt.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

theorem norm_logDeriv_zetaChi_quarter_shift_sub_line_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖logDeriv zetaChi
        (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (linePt tau)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let z : ℂ := linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hzpos : 0 < z.re := by dsimp only [z]; simp [linePt]; norm_num
  have h1zpos : 0 < (1 - z).re := by
    dsimp only [z]
    simp [linePt]
    norm_num
  have hspos : 0 < (linePt tau).re := by rw [linePt_re]; norm_num
  have h1spos : 0 < (1 - linePt tau).re := by
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  rw [show linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I) = z by rfl,
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hzpos)
      (div_two_ne_neg_nat_of_re_pos h1zpos),
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hspos)
      (div_two_ne_neg_nat_of_re_pos h1spos)]
  have hfirst :
      ‖Complex.digamma (z / 2) -
        Complex.digamma (linePt tau / 2)‖ ≤
        (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
    have hz : z / 2 =
        ((3 / 8 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
      dsimp only [z]
      apply Complex.ext <;> simp [linePt] <;> ring
    have hs : linePt tau / 2 =
        ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [linePt] <;> ring
    rw [hz, hs]
    exact norm_digamma_positive_conductor_increment_quarter_le
      htau hv (by norm_num) (by norm_num)
  have hsecond :
      ‖Complex.digamma ((1 - z) / 2) -
        Complex.digamma ((1 - linePt tau) / 2)‖ ≤
        (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
    have hz : (1 - z) / 2 =
        ((1 / 8 : ℝ) : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I := by
      dsimp only [z]
      apply Complex.ext <;> simp [linePt] <;> ring
    have hs : (1 - linePt tau) / 2 =
        ((1 / 4 : ℝ) : ℂ) - ((tau / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [linePt] <;> ring
    rw [hz, hs]
    let a : ℂ := ((1 / 8 : ℝ) : ℂ) +
      (((tau - v) / 2 : ℝ) : ℂ) * I
    let b : ℂ := ((1 / 4 : ℝ) : ℂ) +
      ((tau / 2 : ℝ) : ℂ) * I
    have ha : (starRingEnd ℂ) a =
        ((1 / 8 : ℝ) : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [a, map_div₀, map_ofNat]
    have hb : (starRingEnd ℂ) b =
        ((1 / 4 : ℝ) : ℂ) - ((tau / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [b, map_div₀, map_ofNat]
    rw [← ha, ← hb, ReflectedDigammaAnomaly.digamma_conj,
      ReflectedDigammaAnomaly.digamma_conj, ← map_sub, norm_conj]
    dsimp only [a, b]
    exact norm_digamma_positive_conductor_increment_quarter_le
      htau hv (by norm_num) (by norm_num)
  let A : ℂ := Complex.digamma (z / 2) -
    Complex.digamma (linePt tau / 2)
  let B : ℂ := Complex.digamma ((1 - z) / 2) -
    Complex.digamma ((1 - linePt tau) / 2)
  calc
    ‖-(Complex.digamma (z / 2) / 2) -
          Complex.digamma ((1 - z) / 2) / 2 +
          (Real.log Real.pi : ℂ) -
        (-(Complex.digamma (linePt tau / 2) / 2) -
          Complex.digamma ((1 - linePt tau) / 2) / 2 +
          (Real.log Real.pi : ℂ))‖ =
        ‖-(A / 2) - B / 2‖ := by
      congr 1
      dsimp only [A, B]
      ring
    _ ≤ ‖A / 2‖ + ‖B / 2‖ := by
      simpa only [norm_neg] using norm_sub_le (-(A / 2)) (B / 2)
    _ ≤ ((16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)) / 2 +
        ((16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)) / 2 := by
      apply add_le_add
      · rw [norm_div]
        norm_num
        exact div_le_div_of_nonneg_right
          (by simpa only [A] using hfirst) (by norm_num)
      · rw [norm_div]
        norm_num
        exact div_le_div_of_nonneg_right
          (by simpa only [B] using hsecond) (by norm_num)
    _ = (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by ring


end RHTower
