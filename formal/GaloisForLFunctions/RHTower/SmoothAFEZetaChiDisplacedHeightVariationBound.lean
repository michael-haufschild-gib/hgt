import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedVariationBound

/-!
# Height variation of the displaced chi logarithmic slope

The explicit digamma formula and existing vertical trigamma bounds give conductor-scale variation
of `chi'/chi` along `1/2-d+it`.  Both exact and integration-friendly forms are retained, followed by
the short-window dyadic freezing estimate used by the reflected mollified detector.
-/

noncomputable section

open Complex Set

namespace RHTower

/-- The logarithmic chi slope varies on the conductor scale along one displaced vertical line. -/
theorem norm_logDeriv_zetaChi_displacedLinePt_sub_le
    {d t u : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hu : 4 ≤ u) (htu : 2 * |t - u| ≤ u) :
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt d u)‖ ≤
      2 * (16 / u ^ 2 + 2 * Real.pi / u) * (1 + |t - u|) := by
  have hdhalf : d < 1 / 2 := by linarith
  have htre0 : 0 < (displacedLinePt d t).re := by
    rw [displacedLinePt_re]
    linarith
  have hure0 : 0 < (displacedLinePt d u).re := by
    rw [displacedLinePt_re]
    linarith
  have htonere : 0 < (1 - displacedLinePt d t).re := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    linarith
  have huonere : 0 < (1 - displacedLinePt d u).re := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    linarith
  rw [logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos htre0)
      (div_two_ne_neg_nat_of_re_pos htonere),
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hure0)
      (div_two_ne_neg_nat_of_re_pos huonere)]
  let a : ℝ := 1 / 4 - d / 2
  let b : ℝ := 1 / 4 + d / 2
  let v : ℝ := u - t
  have hv : 2 * |v| ≤ u := by
    dsimp only [v]
    rw [abs_sub_comm]
    exact htu
  have hAt : displacedLinePt d t / 2 =
      (a : ℂ) + (((u - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, a]
      ring
    · norm_num [displacedLinePt, v]
  have hAu : displacedLinePt d u / 2 =
      (a : ℂ) + ((u / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, a]
      ring
    · norm_num [displacedLinePt]
  have hBt : (1 - displacedLinePt d t) / 2 =
      (b : ℂ) - (((u - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, b]
      ring
    · norm_num [displacedLinePt, v]
      ring
  have hBu : (1 - displacedLinePt d u) / 2 =
      (b : ℂ) - ((u / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, b]
      ring
    · norm_num [displacedLinePt]
      ring
  let K : ℝ := 2 * (16 / u ^ 2 + 2 * Real.pi / u) * (1 + |v|)
  have hA :
      ‖Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt d u / 2)‖ ≤ K := by
    rw [hAt, hAu]
    exact norm_digamma_positive_conductor_two_strip_le hu hv
      (by dsimp only [a]; linarith) (by dsimp only [a]; linarith)
      (by dsimp only [a]; linarith) (by dsimp only [a]; linarith)
  have hB :
      ‖Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt d u) / 2)‖ ≤ K := by
    rw [hBt, hBu]
    exact norm_digamma_negative_conductor_two_strip_le hu hv
      (by dsimp only [b]; linarith) (by dsimp only [b]; linarith)
      (by dsimp only [b]; linarith) (by dsimp only [b]; linarith)
  have hvabs : |v| = |t - u| := by
    dsimp only [v]
    rw [abs_sub_comm]
  have hrearr :
      (-(Complex.digamma (displacedLinePt d t / 2) / 2) -
          Complex.digamma ((1 - displacedLinePt d t) / 2) / 2 +
          (Real.log Real.pi : ℂ)) -
        (-(Complex.digamma (displacedLinePt d u / 2) / 2) -
          Complex.digamma ((1 - displacedLinePt d u) / 2) / 2 +
          (Real.log Real.pi : ℂ)) =
        (-(Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt d u / 2)) / 2) -
        (Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt d u) / 2)) / 2 := by ring
  rw [hrearr]
  calc
    _ ≤
        ‖Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt d u / 2)‖ / 2 +
        ‖Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt d u) / 2)‖ / 2 := by
      calc
        _ ≤
            ‖-(Complex.digamma (displacedLinePt d t / 2) -
                Complex.digamma (displacedLinePt d u / 2)) / 2‖ +
              ‖(Complex.digamma ((1 - displacedLinePt d t) / 2) -
                Complex.digamma ((1 - displacedLinePt d u) / 2)) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by
          rw [norm_div, norm_neg, norm_div]
          norm_num
    _ ≤ K / 2 + K / 2 := by gcongr
    _ = 2 * (16 / u ^ 2 + 2 * Real.pi / u) * (1 + |t - u|) := by
      rw [← hvabs]
      dsimp only [K]
      ring

/-- Integration-friendly form of displaced-line logarithmic-slope variation. -/
theorem norm_logDeriv_zetaChi_displacedLinePt_sub_le_coarse
    {d t u : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hu : 4 ≤ u) (htu : 2 * |t - u| ≤ u) :
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt d u)‖ ≤
      (8 + 4 * Real.pi) * (1 + |t - u|) / u := by
  have h := norm_logDeriv_zetaChi_displacedLinePt_sub_le hd hdquarter hu htu
  have hu0 : 0 < u := by linarith
  have hpow : 16 / u ^ 2 ≤ 4 / u := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hu0) hu0]
    nlinarith
  refine h.trans ?_
  calc
    2 * (16 / u ^ 2 + 2 * Real.pi / u) * (1 + |t - u|)
        ≤ 2 * (4 / u + 2 * Real.pi / u) * (1 + |t - u|) := by
          gcongr
    _ = (8 + 4 * Real.pi) * (1 + |t - u|) / u := by
      field_simp
      ring

/-- Uniform freezing bound on a short subwindow of a dyadic block. -/
theorem norm_logDeriv_zetaChi_displacedLinePt_sub_le_dyadic
    {d T t u H : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hT : 4 ≤ T) (hu : u ∈ Set.Icc T (2 * T)) (htu : |t - u| ≤ H)
    (hH : 2 * H ≤ T) :
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt d u)‖ ≤
      (8 + 4 * Real.pi) * (1 + H) / T := by
  have hTu : 0 < T := by linarith
  have hHu : 2 * |t - u| ≤ u := by linarith [hu.1]
  have hbase := norm_logDeriv_zetaChi_displacedLinePt_sub_le_coarse
    hd hdquarter (hT.trans hu.1) hHu
  have hC0 : 0 ≤ 8 + 4 * Real.pi := by positivity
  have hnum0 : 0 ≤ 1 + |t - u| := by positivity
  calc
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt d u)‖ ≤
        (8 + 4 * Real.pi) * (1 + |t - u|) / u := hbase
    _ ≤ (8 + 4 * Real.pi) * (1 + |t - u|) / T := by
      exact div_le_div_of_nonneg_left (mul_nonneg hC0 hnum0) hTu hu.1
    _ ≤ (8 + 4 * Real.pi) * (1 + H) / T := by
      gcongr

end RHTower
