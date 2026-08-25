import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedCombinedMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiDisplacedHeightVariationBound
import GaloisForLFunctions.RHTower.GammaVerticalPhaseAsymptotic

/-!
# Mean-square cost of freezing the reflected logarithmic chi slope

The moving combined reflected detector differs from its frozen version by exactly the base head
times the scalar increment of `chi'/chi`.  This file proves continuity, converts the exact complex
twisted estimate to a positive real energy bound, and prices the moving-coefficient error on a
short dyadic window against the exact gcd-reduced frozen base diagonal.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

theorem continuous_logDeriv_zetaChi_displacedLinePt
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    Continuous (fun t : ℝ => logDeriv zetaChi (displacedLinePt d t)) := by
  have heq : (fun t : ℝ => logDeriv zetaChi (displacedLinePt d t)) =
      fun t : ℝ =>
        -(Complex.digamma (displacedLinePt d t / 2) / 2) -
          Complex.digamma ((1 - displacedLinePt d t) / 2) / 2 +
          (Real.log Real.pi : ℂ) := by
    funext t
    have hsre : 0 < (displacedLinePt d t).re := by
      rw [displacedLinePt_re]
      linarith
    have h1sre : 0 < (1 - displacedLinePt d t).re := by
      rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
      linarith
    exact logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hsre)
      (div_two_ne_neg_nat_of_re_pos h1sre)
  rw [heq]
  rw [continuous_iff_continuousAt]
  intro t
  have hAre : 0 < (displacedLinePt d t / 2).re := by
    rw [Complex.div_re, displacedLinePt_re]
    norm_num
    linarith
  have hBre : 0 < ((1 - displacedLinePt d t) / 2).re := by
    rw [Complex.div_re, Complex.sub_re, Complex.one_re, displacedLinePt_re]
    norm_num
    linarith
  have hA : ContinuousAt
      (fun u : ℝ => Complex.digamma (displacedLinePt d u / 2)) t :=
    ContinuousAt.comp
      (f := fun u : ℝ => displacedLinePt d u / 2)
      (g := Complex.digamma) (continuousAt_digamma hAre) (by
        unfold displacedLinePt
        simp only [div_eq_mul_inv]
        fun_prop)
  have hB : ContinuousAt
      (fun u : ℝ => Complex.digamma ((1 - displacedLinePt d u) / 2)) t :=
    ContinuousAt.comp
      (f := fun u : ℝ => (1 - displacedLinePt d u) / 2)
      (g := Complex.digamma) (continuousAt_digamma hBre) (by
        unfold displacedLinePt
        simp only [div_eq_mul_inv]
        fun_prop)
  fun_prop

/-- Norm of a nonnegative real interval integral after complexification. -/
theorem norm_intervalIntegral_ofReal_eq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    ‖∫ t in a..b, ((f t : ℝ) : ℂ)‖ = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (intervalIntegral.integral_nonneg hab hf)]

/-- Error envelope from the reflected-base twisted mean value. -/
def smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError
    (L M : ℕ) : ℝ :=
  (4 * (L : ℝ) * 1 * ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
    (2 * Real.sqrt M) * (2 * Real.sqrt M)

/-- Exact gcd-reduced diagonal for the reflected-base head and linear mollifier. -/
def smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal
    (d : ℝ) (L M : ℕ) : ℂ :=
  Sieve.mollifiedTwistedDiagonalIcc
    (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
    (smoothAFEZetaDisplacedReflectedBaseNatCoeff d)
    (Sieve.levinsonLinearMollifierCoeff M)
    (Sieve.levinsonLinearMollifierCoeff M) L M 0

/-- Upper form of the exact reflected-base mollified mean value on a positive interval. -/
theorem integral_smoothAFEZetaDisplacedReflectedBase_mollified_normSq_le
    {d : ℝ} (hd : 0 ≤ d) (L M : ℕ) (hM : 1 < M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
      (‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖) ^ 2) ≤
      ‖((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
      smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M := by
  let f : ℝ → ℝ := fun t =>
    (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
  have hmean :=
    integral_smoothAFEZetaDisplacedReflectedBase_mollified_normSq_Icc_error
      hd L M hM a (b - a)
  rw [show a + (b - a) = b by ring] at hmean
  change ‖(∫ t in a..b, (((f t : ℝ) : ℂ))) -
      ((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ ≤
    smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M at hmean
  have hnorm : ‖∫ t in a..b, (((f t : ℝ) : ℂ))‖ =
      ∫ t in a..b, f t :=
    norm_intervalIntegral_ofReal_eq hab (fun t ht => sq_nonneg _)
  change (∫ t in a..b, f t) ≤ _
  rw [← hnorm]
  calc
    ‖∫ t in a..b, (((f t : ℝ) : ℂ))‖ =
        ‖((∫ t in a..b, (((f t : ℝ) : ℂ))) -
            ((b - a : ℝ) : ℂ) *
              smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M) +
          ((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ := by
              congr 1
              ring
    _ ≤ ‖(∫ t in a..b, (((f t : ℝ) : ℂ))) -
            ((b - a : ℝ) : ℂ) *
              smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
          ‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ :=
      norm_add_le _ _
    _ ≤ smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M +
          ‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ := by
      gcongr
    _ = _ := by ring

/-- Moving-minus-frozen combined reflected head, including the literal mollifier. -/
def smoothAFEZetaDisplacedReflectedCombinedFreezingError
    (lam d u : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  (Sieve.dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
        (logDeriv zetaChi (displacedLinePt d t)) n) t -
    Sieve.dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
        (logDeriv zetaChi (displacedLinePt d u)) n) t) *
    Sieve.levinsonLinearMollifier M t

/-- Freezing changes only the base coefficient, by the scalar logarithmic-slope increment. -/
theorem smoothAFEZetaDisplacedReflectedCombinedFreezingError_eq
    (lam d u : ℝ) (L M : ℕ) (t : ℝ) :
    smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t =
      (lam : ℂ) *
        (logDeriv zetaChi (displacedLinePt d t) -
          logDeriv zetaChi (displacedLinePt d u)) *
        (Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t *
          Sieve.levinsonLinearMollifier M t) := by
  rw [smoothAFEZetaDisplacedReflectedCombinedFreezingError,
    sieveDirPoly_smoothAFEZetaDisplacedReflectedCombinedCoeff,
    sieveDirPoly_smoothAFEZetaDisplacedReflectedCombinedCoeff]
  ring

theorem continuous_levinsonLinearMollifier (M : ℕ) :
    Continuous (Sieve.levinsonLinearMollifier M) := by
  have heq : Sieve.levinsonLinearMollifier M =
      fun t : ℝ => Sieve.dirPoly M (levinsonLinearMollifierFinCoeff M) (-t) := by
    funext t
    exact (sieveDirPoly_levinsonLinearMollifierFinCoeff_neg M t).symm
  rw [heq]
  exact (Sieve.continuous_dirPoly M (levinsonLinearMollifierFinCoeff M)).comp
    continuous_id.neg

theorem continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam u : ℝ) (L M : ℕ) :
    Continuous
      (smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M) := by
  have heq : smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M =
      fun t : ℝ =>
        (lam : ℂ) *
          (logDeriv zetaChi (displacedLinePt d t) -
            logDeriv zetaChi (displacedLinePt d u)) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t *
            Sieve.levinsonLinearMollifier M t) := by
    funext t
    exact smoothAFEZetaDisplacedReflectedCombinedFreezingError_eq lam d u L M t
  rw [heq]
  exact (continuous_const.mul
      ((continuous_logDeriv_zetaChi_displacedLinePt hd hdhalf).sub continuous_const)).mul
    ((Sieve.continuous_dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n)).mul
      (continuous_levinsonLinearMollifier M))

/-- Pointwise moving-coefficient error on a short dyadic subwindow. -/
theorem norm_smoothAFEZetaDisplacedReflectedCombinedFreezingError_le_dyadic
    {lam d T t u H : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hT : 4 ≤ T) (hu : u ∈ Set.Icc T (2 * T)) (htu : |t - u| ≤ H)
    (hH : 2 * H ≤ T) (L M : ℕ) :
    ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ≤
      (|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) *
        (‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖) := by
  rw [smoothAFEZetaDisplacedReflectedCombinedFreezingError_eq,
    norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hq := norm_logDeriv_zetaChi_displacedLinePt_sub_le_dyadic
    hd hdquarter hT hu htu hH
  gcongr

/-- Mean-square price of freezing `chi'/chi` on one short dyadic subwindow. The frozen base main
term remains the exact gcd-reduced diagonal. -/
theorem integral_smoothAFEZetaDisplacedReflectedCombinedFreezingError_normSq_le_dyadic
    {lam d T u H a b : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (hT : 4 ≤ T) (huT : u ∈ Set.Icc T (2 * T))
    (hab : a ≤ b) (huab : u ∈ Set.Icc a b) (hwidth : b - a ≤ H)
    (hH : 2 * H ≤ T) (L M : ℕ) (hM : 1 < M) :
    (∫ t in a..b,
      ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2) ≤
      (|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
        (‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
          smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M) := by
  let D : ℝ := |lam| * ((8 + 4 * Real.pi) * (1 + H) / T)
  let g : ℝ → ℝ := fun t =>
    (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2 ≤
        D ^ 2 * g t := by
    intro t ht
    have htu : |t - u| ≤ H := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, huab.1, huab.2, hwidth]
    have hnorm :=
      norm_smoothAFEZetaDisplacedReflectedCombinedFreezingError_le_dyadic
        (lam := lam) hd hdquarter hT huT htu hH L M
    have hD0 : 0 ≤ D := by
      dsimp only [D]
      have hT0 : 0 < T := by linarith
      have hH0 : 0 ≤ H := by linarith [sub_nonneg.mpr hab, hwidth]
      positivity
    have hbase0 : 0 ≤
        ‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    change ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ≤
      D * (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) at hnorm
    change ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2 ≤
      D ^ 2 * (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
    nlinarith [norm_nonneg
      (smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t)]
  have hcontErr :=
    continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
      hd (hdquarter.trans_lt (by norm_num)) lam u L M
  have hcontG : Continuous g := by
    dsimp only [g]
    exact (((Sieve.continuous_dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n)).norm.mul
        (continuous_levinsonLinearMollifier M).norm).pow 2)
  have hmono :
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2) ≤
      ∫ t in a..b, D ^ 2 * g t := by
    have hintErr : IntervalIntegrable
        (fun t =>
          ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2)
        MeasureTheory.volume a b := by
      have hsquare := (hcontErr.norm.mul hcontErr.norm).intervalIntegrable
        (μ := MeasureTheory.volume) a b
      have heq :
          (fun t =>
            ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2) =
          (fun t =>
            ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ *
            ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖) := by
        funext t
        rw [pow_two]
      rw [heq]
      convert hsquare using 1
      funext t
      rfl
    have hintG : IntervalIntegrable (fun t => D ^ 2 * g t)
        MeasureTheory.volume a b :=
      (continuous_const.mul hcontG).intervalIntegrable a b
    exact intervalIntegral.integral_mono_on hab
      hintErr hintG hpoint
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hbase := integral_smoothAFEZetaDisplacedReflectedBase_mollified_normSq_le
    hd.le L M hM hab
  change D ^ 2 * (∫ t in a..b, g t) ≤ _
  exact mul_le_mul_of_nonneg_left hbase (sq_nonneg D)

end RHTower
