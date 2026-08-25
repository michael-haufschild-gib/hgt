import GaloisForLFunctions.RHTower.OscillatoryIntegralComplexAmplitude
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiDisplacedHeightVariationBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedChiWeightedMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDetectorEnergyDecomposition

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact vertical derivative of the displaced chi factor in logarithmic-derivative form. -/
theorem hasDerivAt_zetaChi_displacedLinePt_logDeriv
    {d : ℝ} (hd : 0 ≤ d) (hdhalf : d < 1 / 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => zetaChi (displacedLinePt d u))
      (zetaChi (displacedLinePt d t) *
        (I * logDeriv zetaChi (displacedLinePt d t))) t := by
  have hG : Gammaℝ (1 - displacedLinePt d t) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith
  have hout : HasDerivAt zetaChi (deriv zetaChi (displacedLinePt d t))
      (displacedLinePt d t) :=
    (zetaChi_analyticAt hG).differentiableAt.hasDerivAt
  have hcomp := hout.scomp t (hasDerivAt_displacedLinePt d t)
  change HasDerivAt (fun u : ℝ => zetaChi (displacedLinePt d u))
    (I • deriv zetaChi (displacedLinePt d t)) t at hcomp
  have hne : zetaChi (displacedLinePt d t) ≠ 0 := by
    apply zetaChi_ne_zero_of_mem_openStrip
    · rw [displacedLinePt_re]
      linarith
    · rw [displacedLinePt_re]
      linarith
  have hderiv : deriv zetaChi (displacedLinePt d t) =
      logDeriv zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d t) := by
    simp [logDeriv, hne]
  have hcomp' : HasDerivAt (fun u : ℝ => zetaChi (displacedLinePt d u))
      (I * deriv zetaChi (displacedLinePt d t)) t := by
    simpa only [smul_eq_mul] using hcomp
  convert hcomp' using 1
  rw [hderiv]
  ring

/-- Ratio of displaced chi to critical-line chi; this isolates the slow complex amplitude. -/
def zetaChiDisplacedCriticalRatio (d t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) / zetaChi (displacedLinePt 0 t)

theorem hasDerivAt_zetaChiDisplacedCriticalRatio
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (t : ℝ) :
    HasDerivAt (zetaChiDisplacedCriticalRatio d)
      (zetaChiDisplacedCriticalRatio d t *
        (I * (logDeriv zetaChi (displacedLinePt d t) -
          logDeriv zetaChi (displacedLinePt 0 t)))) t := by
  have hnum := hasDerivAt_zetaChi_displacedLinePt_logDeriv hd.le hdhalf t
  have hden0 := hasDerivAt_zetaChi_displacedLinePt_logDeriv
    (d := 0) (by norm_num) (by norm_num) t
  have hpt : displacedLinePt 0 t = linePt t := by
    simp [displacedLinePt, linePt]
  have hne : zetaChi (displacedLinePt 0 t) ≠ 0 := by
    rw [hpt]
    exact zetaChi_line_ne_zero t
  have hquot := hnum.div hden0 hne
  change HasDerivAt (zetaChiDisplacedCriticalRatio d)
    ((zetaChi (displacedLinePt d t) *
          (I * logDeriv zetaChi (displacedLinePt d t)) *
        zetaChi (displacedLinePt 0 t) -
      zetaChi (displacedLinePt d t) *
        (zetaChi (displacedLinePt 0 t) *
          (I * logDeriv zetaChi (displacedLinePt 0 t)))) /
      zetaChi (displacedLinePt 0 t) ^ 2) t at hquot
  convert hquot using 1
  rw [zetaChiDisplacedCriticalRatio]
  field_simp [hne]

/-- Critical-line chi logarithmic derivative is the real Hardy phase rate. -/
theorem logDeriv_zetaChi_displacedLinePt_zero_eq (t : ℝ) :
    logDeriv zetaChi (displacedLinePt 0 t) =
      ((-2 * gammaHardyPhaseRate t : ℝ) : ℂ) := by
  have hlog := hasDerivAt_zetaChi_displacedLinePt_logDeriv
    (d := 0) (by norm_num) (by norm_num) t
  have hreal : HasDerivAt (fun u : ℝ => -2 * gammaHardyTheta u)
      (-2 * gammaHardyPhaseRate t) t := by
    simpa using (hasDerivAt_gammaHardyTheta t).const_mul (-2)
  have hphase0 := (hreal.ofReal_comp.mul_const I).cexp
  have hfun : (fun u : ℝ => zetaChi (displacedLinePt 0 u)) =
      fun u : ℝ => Complex.exp (((-2 * gammaHardyTheta u : ℝ) : ℂ) * I) := by
    funext u
    have hpt : displacedLinePt 0 u = linePt u := by
      simp [displacedLinePt, linePt]
    rw [hpt, zetaChi_line_eq_exp_neg_two_theta]
    congr 1
    push_cast
    ring
  have hval := congrFun hfun t
  rw [← hfun] at hphase0
  rw [← hval] at hphase0
  have hder := hlog.unique hphase0
  have hpt : displacedLinePt 0 t = linePt t := by
    simp [displacedLinePt, linePt]
  have hne : zetaChi (displacedLinePt 0 t) ≠ 0 := by
    rw [hpt]
    exact zetaChi_line_ne_zero t
  have hcancel :
      (zetaChi (displacedLinePt 0 t) * I) *
          logDeriv zetaChi (displacedLinePt 0 t) =
        (zetaChi (displacedLinePt 0 t) * I) *
          (((-2 * gammaHardyPhaseRate t : ℝ) : ℂ)) := by
    calc
      _ = zetaChi (displacedLinePt 0 t) *
          (I * logDeriv zetaChi (displacedLinePt 0 t)) := by ring
      _ = zetaChi (displacedLinePt 0 t) *
          (((-2 * gammaHardyPhaseRate t : ℝ) : ℂ) * I) := hder
      _ = _ := by ring
  exact mul_left_cancel₀ (mul_ne_zero hne Complex.I_ne_zero) hcancel

theorem continuous_logDeriv_zetaChi_displacedLinePt_zero :
    Continuous (fun t : ℝ => logDeriv zetaChi (displacedLinePt 0 t)) := by
  have heq : (fun t : ℝ => logDeriv zetaChi (displacedLinePt 0 t)) =
      fun t : ℝ => ((-2 * gammaHardyPhaseRate t : ℝ) : ℂ) := by
    funext t
    exact logDeriv_zetaChi_displacedLinePt_zero_eq t
  rw [heq]
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul continuous_gammaHardyPhaseRate)

/-- Horizontal displacement changes the chi logarithmic slope by `O(1/t)`, with exact constants. -/
theorem norm_logDeriv_zetaChi_displaced_sub_critical_le
    {d t : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4) (ht : 4 ≤ t) :
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt 0 t)‖ ≤
      2 * (16 / t ^ 2 + 2 * Real.pi / t) := by
  have hdre : 0 < (displacedLinePt d t).re := by
    rw [displacedLinePt_re]
    linarith
  have hdonere : 0 < (1 - displacedLinePt d t).re := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    linarith
  have h0re : 0 < (displacedLinePt 0 t).re := by
    rw [displacedLinePt_re]
    norm_num
  have h0onere : 0 < (1 - displacedLinePt 0 t).re := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    norm_num
  rw [logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hdre)
      (div_two_ne_neg_nat_of_re_pos hdonere),
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos h0re)
      (div_two_ne_neg_nat_of_re_pos h0onere)]
  let a : ℝ := 1 / 4 - d / 2
  let b : ℝ := 1 / 4 + d / 2
  have hv : 2 * |(0 : ℝ)| ≤ t := by simp; linarith
  have hAd : displacedLinePt d t / 2 =
      (a : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, a]
      ring
    · norm_num [displacedLinePt]
  have hA0 : displacedLinePt 0 t / 2 =
      ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
    · norm_num [displacedLinePt]
  have hBd : (1 - displacedLinePt d t) / 2 =
      (b : ℂ) - ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt, b]
      ring
    · norm_num [displacedLinePt]
      ring
  have hB0 : (1 - displacedLinePt 0 t) / 2 =
      ((1 / 4 : ℝ) : ℂ) - ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
    · norm_num [displacedLinePt]
      ring
  have hA :
      ‖Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt 0 t / 2)‖ ≤
        2 * (16 / t ^ 2 + 2 * Real.pi / t) := by
    rw [hAd, hA0]
    simpa using norm_digamma_positive_conductor_two_strip_le ht hv
      (a := a) (b := 1 / 4)
      (by dsimp only [a]; linarith) (by dsimp only [a]; linarith)
      (by norm_num) (by norm_num)
  have hB :
      ‖Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt 0 t) / 2)‖ ≤
        2 * (16 / t ^ 2 + 2 * Real.pi / t) := by
    rw [hBd, hB0]
    simpa using norm_digamma_negative_conductor_two_strip_le ht hv
      (a := b) (b := 1 / 4)
      (by dsimp only [b]; linarith) (by dsimp only [b]; linarith)
      (by norm_num) (by norm_num)
  have hrearr :
      (-(Complex.digamma (displacedLinePt d t / 2) / 2) -
          Complex.digamma ((1 - displacedLinePt d t) / 2) / 2 +
          (Real.log Real.pi : ℂ)) -
        (-(Complex.digamma (displacedLinePt 0 t / 2) / 2) -
          Complex.digamma ((1 - displacedLinePt 0 t) / 2) / 2 +
          (Real.log Real.pi : ℂ)) =
        (-(Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt 0 t / 2)) / 2) -
        (Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt 0 t) / 2)) / 2 := by ring
  rw [hrearr]
  calc
    _ ≤
        ‖Complex.digamma (displacedLinePt d t / 2) -
          Complex.digamma (displacedLinePt 0 t / 2)‖ / 2 +
        ‖Complex.digamma ((1 - displacedLinePt d t) / 2) -
          Complex.digamma ((1 - displacedLinePt 0 t) / 2)‖ / 2 := by
      calc
        _ ≤
            ‖-(Complex.digamma (displacedLinePt d t / 2) -
                Complex.digamma (displacedLinePt 0 t / 2)) / 2‖ +
              ‖(Complex.digamma ((1 - displacedLinePt d t) / 2) -
                Complex.digamma ((1 - displacedLinePt 0 t) / 2)) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by
          rw [norm_div, norm_neg, norm_div]
          norm_num
    _ ≤ (2 * (16 / t ^ 2 + 2 * Real.pi / t)) / 2 +
          (2 * (16 / t ^ 2 + 2 * Real.pi / t)) / 2 := by gcongr
    _ = 2 * (16 / t ^ 2 + 2 * Real.pi / t) := by ring

theorem norm_logDeriv_zetaChi_displaced_sub_critical_le_coarse
    {d t : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4) (ht : 4 ≤ t) :
    ‖logDeriv zetaChi (displacedLinePt d t) -
        logDeriv zetaChi (displacedLinePt 0 t)‖ ≤
      (8 + 4 * Real.pi) / t := by
  have h := norm_logDeriv_zetaChi_displaced_sub_critical_le hd hdquarter ht
  have ht0 : 0 < t := by linarith
  have hpow : 16 / t ^ 2 ≤ 4 / t := by
    rw [div_le_div_iff₀ (sq_pos_of_pos ht0) ht0]
    nlinarith
  refine h.trans ?_
  calc
    2 * (16 / t ^ 2 + 2 * Real.pi / t)
        ≤ 2 * (4 / t + 2 * Real.pi / t) := by gcongr
    _ = (8 + 4 * Real.pi) / t := by
      field_simp
      ring

theorem norm_zetaChiDisplacedCriticalRatio (d t : ℝ) :
    ‖zetaChiDisplacedCriticalRatio d t‖ =
      ‖zetaChi (displacedLinePt d t)‖ := by
  have hpt : displacedLinePt 0 t = linePt t := by
    simp [displacedLinePt, linePt]
  rw [zetaChiDisplacedCriticalRatio, norm_div, hpt, norm_zetaChi_line, div_one]

theorem continuous_zetaChiDisplacedCriticalRatio
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    Continuous (zetaChiDisplacedCriticalRatio d) := by
  have hnum := continuous_zetaChi_displacedLinePt hd hdhalf
  have hline : Continuous (fun t : ℝ => zetaChi (linePt t)) := by
    simpa using (continuous_zetaChiCriticalTwistIntegrand 0)
  have hden : Continuous (fun t : ℝ => zetaChi (displacedLinePt 0 t)) := by
    have heq : (fun t : ℝ => zetaChi (displacedLinePt 0 t)) =
        fun t : ℝ => zetaChi (linePt t) := by
      funext t
      congr 2
      simp [displacedLinePt, linePt]
    rw [heq]
    exact hline
  unfold zetaChiDisplacedCriticalRatio
  exact hnum.div hden (fun t => by
    have hpt : displacedLinePt 0 t = linePt t := by
      simp [displacedLinePt, linePt]
    rw [hpt]
    exact zetaChi_line_ne_zero t)

/-- Exact derivative field of the slow displaced-to-critical chi ratio. -/
def zetaChiDisplacedCriticalRatioDeriv (d t : ℝ) : ℂ :=
  zetaChiDisplacedCriticalRatio d t *
    (I * (logDeriv zetaChi (displacedLinePt d t) -
      logDeriv zetaChi (displacedLinePt 0 t)))

theorem continuous_zetaChiDisplacedCriticalRatioDeriv
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    Continuous (zetaChiDisplacedCriticalRatioDeriv d) := by
  unfold zetaChiDisplacedCriticalRatioDeriv
  exact (continuous_zetaChiDisplacedCriticalRatio hd hdhalf).mul
    (continuous_const.mul
      ((continuous_logDeriv_zetaChi_displacedLinePt hd hdhalf).sub
        continuous_logDeriv_zetaChi_displacedLinePt_zero))

theorem hasDerivAt_zetaChiDisplacedCriticalRatio'
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (t : ℝ) :
    HasDerivAt (zetaChiDisplacedCriticalRatio d)
      (zetaChiDisplacedCriticalRatioDeriv d t) t := by
  exact hasDerivAt_zetaChiDisplacedCriticalRatio hd hdhalf t

theorem norm_zetaChiDisplacedCriticalRatioDeriv_le_dyadic
    {K d T t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hT : 4 ≤ T) (ht : t ∈ Set.Icc T (2 * T))
    (hchi : ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d) :
    ‖zetaChiDisplacedCriticalRatioDeriv d t‖ ≤
      (K * (2 * T) ^ d) * ((8 + 4 * Real.pi) / T) := by
  have ht4 : 4 ≤ t := hT.trans ht.1
  have hs0 :=
    norm_logDeriv_zetaChi_displaced_sub_critical_le_coarse hd hdquarter ht4
  have hT0 : 0 < T := by linarith
  have hC0 : 0 ≤ 8 + 4 * Real.pi := by positivity
  have hs :
      ‖logDeriv zetaChi (displacedLinePt d t) -
          logDeriv zetaChi (displacedLinePt 0 t)‖ ≤
        (8 + 4 * Real.pi) / T :=
    hs0.trans (div_le_div_of_nonneg_left hC0 hT0 ht.1)
  have hcarrier0 : 0 ≤ K * (2 * T) ^ d :=
    mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
  rw [zetaChiDisplacedCriticalRatioDeriv, norm_mul, norm_mul,
    norm_I, one_mul, norm_zetaChiDisplacedCriticalRatio]
  exact mul_le_mul hchi hs (norm_nonneg _) hcarrier0

theorem integral_norm_zetaChiDisplacedCriticalRatioDeriv_le_dyadic
    {K d T : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hT : 4 ≤ T)
    (hchi : ∀ t ∈ Set.Icc T (2 * T),
      ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d) :
    (∫ t in T..(2 * T), ‖zetaChiDisplacedCriticalRatioDeriv d t‖) ≤
      (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2 * T := by linarith
  have hcont := continuous_zetaChiDisplacedCriticalRatioDeriv hd hdhalf
  have hpoint : ∀ t ∈ Set.Icc T (2 * T),
      ‖zetaChiDisplacedCriticalRatioDeriv d t‖ ≤
        (K * (2 * T) ^ d) * ((8 + 4 * Real.pi) / T) := by
    intro t ht
    exact norm_zetaChiDisplacedCriticalRatioDeriv_le_dyadic
      hK hd hdquarter hT ht (hchi t ht)
  have hmono := intervalIntegral.integral_mono_on hab
    (hcont.norm.intervalIntegrable (μ := volume) T (2 * T))
    (intervalIntegrable_const (μ := volume)) hpoint
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [hT0.ne']
  ring

/-- Unconditional displaced-line stationary-frequency bound.  The critical chi phase supplies
square-root cancellation; horizontal displacement appears only through the expected `T^d` size. -/
theorem exists_norm_integral_zetaChi_displacedLinePt_mul_exp_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T : ℝ, 4 ≤ T → ∀ ω : ℝ,
        ‖∫ t in T..(2 * T),
            zetaChi (displacedLinePt d t) *
              Complex.exp (((ω * t : ℝ) : ℂ) * I)‖ ≤
          (6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) := by
  have hd₀half : d₀ < 1 / 2 := hd₀quarter.trans_lt (by norm_num)
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_displacedLinePt_le_dyadic hd₀0 hd₀half
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T hT ω
  have hdquarter : d ≤ 1 / 4 := hdd₀.trans hd₀quarter
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  let u : ℝ → ℂ := zetaChiDisplacedCriticalRatio d
  let u' : ℝ → ℂ := zetaChiDisplacedCriticalRatioDeriv d
  have hu : ∀ t ∈ Set.uIcc T (2 * T), HasDerivAt u (u' t) t := by
    intro t ht
    exact hasDerivAt_zetaChiDisplacedCriticalRatio' hd hdhalf t
  have hu' : IntervalIntegrable u' volume T (2 * T) :=
    (continuous_zetaChiDisplacedCriticalRatioDeriv hd hdhalf).intervalIntegrable T (2 * T)
  have hstationary :=
    norm_integral_complexAmplitude_mul_zetaChi_line_mul_exp_le hT ω hu hu'
  have heq :
      (∫ t in T..(2 * T),
        zetaChi (displacedLinePt d t) *
          Complex.exp (((ω * t : ℝ) : ℂ) * I)) =
      ∫ t in T..(2 * T),
        u t * (zetaChi (linePt t) *
          Complex.exp (((ω * t : ℝ) : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hpt : displacedLinePt 0 t = linePt t := by
      simp [displacedLinePt, linePt]
    have hne : zetaChi (linePt t) ≠ 0 := zetaChi_line_ne_zero t
    dsimp only [u]
    rw [zetaChiDisplacedCriticalRatio, hpt]
    field_simp [hne]
  rw [heq]
  refine hstationary.trans ?_
  have hchiBlock : ∀ t ∈ Set.Icc T (2 * T),
      ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d := by
    intro t ht
    exact hchi d hd.le hdd₀ T t (by linarith) ht
  have hEnd : ‖u (2 * T)‖ ≤ K * (2 * T) ^ d := by
    dsimp only [u]
    rw [norm_zetaChiDisplacedCriticalRatio]
    exact hchiBlock (2 * T) ⟨by linarith, le_rfl⟩
  have hVar :
      (∫ t in T..(2 * T), ‖u' t‖) ≤
        (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := by
    exact integral_norm_zetaChiDisplacedCriticalRatioDeriv_le_dyadic
      hK hd hdquarter hT hchiBlock
  have hsum :
      ‖u (2 * T)‖ + ∫ t in T..(2 * T), ‖u' t‖ ≤
        (K * (2 * T) ^ d) * (9 + 4 * Real.pi) := by
    calc
      _ ≤ (K * (2 * T) ^ d) +
          (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := add_le_add hEnd hVar
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end

end RHTower
