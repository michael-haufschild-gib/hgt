import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedDerivative
import GaloisForLFunctions.HTGeometry.DigammaPositiveStripLinearBound

/-!
# Global derivative envelope for displaced chi ratios

All four digamma arguments produced by a displaced negative-contour shift
remain in one compact positive strip.  Their uniform linear envelope gives
the polynomial domination needed to differentiate the displaced dual weight.
-/

noncomputable section

namespace RHTower

open Complex

theorem logDeriv_zetaChi_displaced_neg_shift_sub_eq_digamma_increments
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) (τ v : ℝ) :
    logDeriv zetaChi
        (displacedLinePt d τ -
          (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (displacedLinePt d τ) =
      -(Complex.digamma
          ((displacedLinePt d τ -
            (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (displacedLinePt d τ / 2)) / 2 -
        (Complex.digamma
          ((1 - (displacedLinePt d τ -
            (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - displacedLinePt d τ) / 2)) / 2 := by
  let zR : ℂ := displacedLinePt d τ -
    (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)
  let zL : ℂ := displacedLinePt d τ
  have hzRre : zR.re = 1 / 2 + η := by
    dsimp only [zR]
    simp [displacedLinePt]
    ring
  have hzLre : zL.re = 1 / 2 - d := by
    dsimp only [zL]
    exact displacedLinePt_re d τ
  have hzR0 : 0 < zR.re := by rw [hzRre]; linarith
  have h1zR0 : 0 < (1 - zR).re := by rw [Complex.sub_re, Complex.one_re, hzRre]; linarith
  have hzL0 : 0 < zL.re := by rw [hzLre]; linarith
  have h1zL0 : 0 < (1 - zL).re := by rw [Complex.sub_re, Complex.one_re, hzLre]; linarith
  rw [show displacedLinePt d τ -
      (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I) = zR by rfl,
    show displacedLinePt d τ = zL by rfl,
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hzR0)
      (div_two_ne_neg_nat_of_re_pos h1zR0),
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hzL0)
      (div_two_ne_neg_nat_of_re_pos h1zL0)]
  ring

theorem exists_norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_global
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ τ v : ℝ,
      ‖logDeriv zetaChi
          (displacedLinePt d τ -
            (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (displacedLinePt d τ)‖ ≤
        D * (1 + |τ|) * (1 + |v|) := by
  let δ : ℝ := max d₀ η
  let a : ℝ := 1 / 4 - δ / 2
  let b : ℝ := 1 / 4 + δ / 2
  have hδhalf : δ < 1 / 2 := by
    dsimp only [δ]
    exact max_lt hd₀half hηhalf
  have ha : 0 < a := by dsimp only [a]; linarith
  have hab : a ≤ b := by dsimp only [a, b]; linarith [le_max_left d₀ η]
  obtain ⟨K, hK, hstrip⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_positive_strip_le ha hab
  let D : ℝ := 2 * K
  refine ⟨D, by dsimp only [D]; positivity, fun d hd hdd₀ τ v => ?_⟩
  have hdhalf : d < 1 / 2 := hdd₀.trans_lt hd₀half
  rw [logDeriv_zetaChi_displaced_neg_shift_sub_eq_digamma_increments
    hd hdhalf hη hηhalf]
  let A : ℂ := Complex.digamma
    ((displacedLinePt d τ -
      (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) / 2)
  let B : ℂ := Complex.digamma (displacedLinePt d τ / 2)
  let C : ℂ := Complex.digamma
    ((1 - (displacedLinePt d τ -
      (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))) / 2)
  let E : ℂ := Complex.digamma ((1 - displacedLinePt d τ) / 2)
  have hδd : d ≤ δ := hdd₀.trans (le_max_left d₀ η)
  have hδη : η ≤ δ := le_max_right d₀ η
  have hAarg :
      (displacedLinePt d τ -
        (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
        ((1 / 4 + η / 2 : ℝ) : ℂ) +
          (((τ - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]; ring
    · norm_num [displacedLinePt]
  have hBarg : displacedLinePt d τ / 2 =
      ((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]; ring
    · norm_num [displacedLinePt]
  have hCarg :
      (1 - (displacedLinePt d τ -
        (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
        ((1 / 4 - η / 2 : ℝ) : ℂ) +
          (((-(τ - v)) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]; ring
    · norm_num [displacedLinePt]
  have hEarg : (1 - displacedLinePt d τ) / 2 =
      ((1 / 4 + d / 2 : ℝ) : ℂ) + (((-τ) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]; ring
    · norm_num [displacedLinePt]
  have hA : ‖A‖ ≤ K * (1 + |(τ - v) / 2|) := by
    dsimp only [A]
    rw [hAarg]
    exact hstrip (1 / 4 + η / 2) (by dsimp only [a]; linarith)
      (by dsimp only [b]; linarith) ((τ - v) / 2)
  have hB : ‖B‖ ≤ K * (1 + |τ / 2|) := by
    dsimp only [B]
    rw [hBarg]
    exact hstrip (1 / 4 - d / 2) (by dsimp only [a]; linarith)
      (by dsimp only [b]; linarith) (τ / 2)
  have hC : ‖C‖ ≤ K * (1 + |(-(τ - v)) / 2|) := by
    dsimp only [C]
    rw [hCarg]
    exact hstrip (1 / 4 - η / 2) (by dsimp only [a]; linarith)
      (by dsimp only [b]; linarith) (-(τ - v) / 2)
  have hE : ‖E‖ ≤ K * (1 + |(-τ) / 2|) := by
    dsimp only [E]
    rw [hEarg]
    exact hstrip (1 / 4 + d / 2) (by dsimp only [a]; linarith)
      (by dsimp only [b]; linarith) ((-τ) / 2)
  have hheight :
      (1 + |(τ - v) / 2|) + (1 + |τ / 2|) ≤
        2 + |τ| + |v| := by
    rw [abs_div, abs_div]
    norm_num
    nlinarith [abs_sub τ v, abs_nonneg τ, abs_nonneg v]
  have hheightNeg :
      (1 + |(-(τ - v)) / 2|) + (1 + |(-τ) / 2|) ≤
        2 + |τ| + |v| := by
    simpa only [neg_div, abs_neg] using hheight
  have hAB : ‖A - B‖ ≤ K * (2 + |τ| + |v|) := by
    calc
      ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(τ - v) / 2|) + K * (1 + |τ / 2|) :=
        add_le_add hA hB
      _ = K * ((1 + |(τ - v) / 2|) + (1 + |τ / 2|)) := by ring
      _ ≤ K * (2 + |τ| + |v|) := mul_le_mul_of_nonneg_left hheight hK
  have hCE : ‖C - E‖ ≤ K * (2 + |τ| + |v|) := by
    calc
      ‖C - E‖ ≤ ‖C‖ + ‖E‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(-(τ - v)) / 2|) + K * (1 + |(-τ) / 2|) :=
        add_le_add hC hE
      _ = K * ((1 + |(-(τ - v)) / 2|) + (1 + |(-τ) / 2|)) := by ring
      _ ≤ K * (2 + |τ| + |v|) := mul_le_mul_of_nonneg_left hheightNeg hK
  have hprod : 2 + |τ| + |v| ≤ 2 * (1 + |τ|) * (1 + |v|) := by
    nlinarith [abs_nonneg τ, abs_nonneg v,
      mul_nonneg (abs_nonneg τ) (abs_nonneg v)]
  change ‖-(A - B) / 2 - (C - E) / 2‖ ≤ _
  calc
    ‖-(A - B) / 2 - (C - E) / 2‖
        ≤ ‖-(A - B) / 2‖ + ‖(C - E) / 2‖ := norm_sub_le _ _
    _ = ‖A - B‖ / 2 + ‖C - E‖ / 2 := by
      rw [norm_div, norm_neg, norm_div]
      norm_num
    _ ≤ (K * (2 + |τ| + |v|)) / 2 +
          (K * (2 + |τ| + |v|)) / 2 := by gcongr
    _ = K * (2 + |τ| + |v|) := by ring
    _ ≤ K * (2 * (1 + |τ|) * (1 + |v|)) :=
      mul_le_mul_of_nonneg_left hprod hK
    _ = D * (1 + |τ|) * (1 + |v|) := by dsimp only [D]; ring

end RHTower
