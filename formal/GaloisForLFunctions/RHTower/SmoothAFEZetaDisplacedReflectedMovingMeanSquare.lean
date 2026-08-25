import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedChiWeightedMeanSquare

/-!
# Actual moving chi-weighted reflected-head mean square

Combines the literal moving logarithmic chi slope, the functional-equation chi factor, and the
linear mollifier.  On a short dyadic window its energy is bounded by the exact frozen combined
diagonal plus the already isolated coefficient-freezing energy.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Moving combined reflected carrier before multiplication by the chi factor. -/
def smoothAFEZetaDisplacedReflectedMovingCarrier
    (lam d : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  Sieve.dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
        (logDeriv zetaChi (displacedLinePt d t)) n) t *
    Sieve.levinsonLinearMollifier M t

/-- Literal chi-weighted moving combined reflected detector head. -/
def smoothAFEZetaDisplacedReflectedMovingHead
    (lam d : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) *
    smoothAFEZetaDisplacedReflectedMovingCarrier lam d L M t

/-- Exact moving carrier decomposition into a frozen carrier and its isolated error. -/
theorem smoothAFEZetaDisplacedReflectedMovingCarrier_eq_frozen_add_error
    (lam d u : ℝ) (L M : ℕ) (t : ℝ) :
    smoothAFEZetaDisplacedReflectedMovingCarrier lam d L M t =
      Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
            (logDeriv zetaChi (displacedLinePt d u)) n) t *
        Sieve.levinsonLinearMollifier M t +
      smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t := by
  rw [smoothAFEZetaDisplacedReflectedMovingCarrier,
    smoothAFEZetaDisplacedReflectedCombinedFreezingError]
  ring

theorem continuous_smoothAFEZetaDisplacedReflectedMovingCarrier
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam : ℝ) (L M : ℕ) :
    Continuous (smoothAFEZetaDisplacedReflectedMovingCarrier lam d L M) := by
  have heq : smoothAFEZetaDisplacedReflectedMovingCarrier lam d L M =
      fun t : ℝ =>
        Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
              (logDeriv zetaChi (displacedLinePt d 0)) n) t *
          Sieve.levinsonLinearMollifier M t +
        smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d 0 L M t := by
    funext t
    exact smoothAFEZetaDisplacedReflectedMovingCarrier_eq_frozen_add_error
      lam d 0 L M t
  rw [heq]
  exact ((Sieve.continuous_dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
        (logDeriv zetaChi (displacedLinePt d 0)) n)).mul
      (continuous_levinsonLinearMollifier M)).add
    (continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
      hd hdhalf lam 0 L M)

/-- Pointwise actual reflected-head estimate after freezing only `chi'/chi`; the chi factor is
bounded uniformly on the ambient dyadic block. -/
theorem norm_smoothAFEZetaDisplacedReflectedMovingHead_le_dyadic
    {K lam d T t u : ℝ}
    (hchi : ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d)
    (L M : ℕ) :
    ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ≤
      (K * (2 * T) ^ d) *
        (‖Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
                (logDeriv zetaChi (displacedLinePt d u)) n) t *
            Sieve.levinsonLinearMollifier M t‖ +
          ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError
            lam d u L M t‖) := by
  rw [smoothAFEZetaDisplacedReflectedMovingHead,
    smoothAFEZetaDisplacedReflectedMovingCarrier_eq_frozen_add_error, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hchi
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- Actual chi-weighted moving reflected-head energy on a short dyadic subwindow.  The supplied
constant and all coefficient bounds are obtained from unconditional prior theorems; main terms
remain the exact frozen combined and reflected-base gcd diagonals. -/
theorem exists_integral_smoothAFEZetaDisplacedReflectedMovingHead_normSq_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℝ), 0 < d → d ≤ d₀ → d ≤ 1 / 4 →
      ∀ (lam T u H a b : ℝ) (L M : ℕ),
        4 ≤ T → u ∈ Set.Icc T (2 * T) → a ≤ b → T ≤ a → b ≤ 2 * T →
        u ∈ Set.Icc a b → b - a ≤ H → 2 * H ≤ T → 1 < M →
        (∫ t in a..b,
          ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2) ≤
          2 * (K * (2 * T) ^ d) ^ 2 *
            ((‖((b - a : ℝ) : ℂ) *
                smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d
                  (logDeriv zetaChi (displacedLinePt d u)) L M‖ +
              smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam
                (logDeriv zetaChi (displacedLinePt d u)) L M) +
            (|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
              (‖((b - a : ℝ) : ℂ) *
                  smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
                smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M)) := by
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_displacedLinePt_le_dyadic hd₀0 hd₀half
  refine ⟨K, hK, fun d hd hdd₀ hdquarter lam T u H a b L M
    hT huT hab haT hbT huab hwidth hH hM => ?_⟩
  let C : ℝ := K * (2 * T) ^ d
  let D : ℝ := |lam| * ((8 + 4 * Real.pi) * (1 + H) / T)
  let f : ℝ → ℝ := fun t =>
    (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
            (logDeriv zetaChi (displacedLinePt d u)) n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
  let e : ℝ → ℝ := fun t =>
    ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖ ^ 2
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2 ≤
        2 * C ^ 2 * (f t + e t) := by
    intro t ht
    have htT : t ∈ Set.Icc T (2 * T) := ⟨haT.trans ht.1, ht.2.trans hbT⟩
    have hz := hchi d hd.le hdd₀ T t (by linarith) htT
    have hnorm := norm_smoothAFEZetaDisplacedReflectedMovingHead_le_dyadic
      (lam := lam) (u := u) hz L M
    let x : ℝ := ‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
            (logDeriv zetaChi (displacedLinePt d u)) n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖
    let y : ℝ := ‖smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t‖
    have hx0 : 0 ≤ x := by dsimp only [x]; positivity
    have hy0 : 0 ≤ y := by dsimp only [y]; positivity
    have hright0 : 0 ≤ C * (x + y) := mul_nonneg hC0 (add_nonneg hx0 hy0)
    rw [norm_mul] at hnorm
    change ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ≤
      C * (x + y) at hnorm
    change ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2 ≤
      2 * C ^ 2 * (x ^ 2 + y ^ 2)
    nlinarith [norm_nonneg (smoothAFEZetaDisplacedReflectedMovingHead lam d L M t),
      sq_nonneg (x - y)]
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  have hcarrierCont :=
    continuous_smoothAFEZetaDisplacedReflectedMovingCarrier hd hdhalf lam L M
  have hchiCont := continuous_norm_zetaChi_left_line hd hdhalf
  have hheadCont : Continuous
      (fun t : ℝ => ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2) := by
    have heq :
        (fun t : ℝ => ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2) =
        fun t : ℝ =>
          (‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ *
            ‖smoothAFEZetaDisplacedReflectedMovingCarrier lam d L M t‖) ^ 2 := by
      funext t
      simp [smoothAFEZetaDisplacedReflectedMovingHead, displacedLinePt]
    rw [heq]
    exact (hchiCont.mul hcarrierCont.norm).pow 2
  have hdirCont :=
    (Sieve.continuous_dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
        (logDeriv zetaChi (displacedLinePt d u)) n)).norm
  have hmollCont := (continuous_levinsonLinearMollifier M).norm
  have hfCont : Continuous f := by
    dsimp only [f]
    exact (hdirCont.mul hmollCont).pow 2
  have heCont : Continuous e := by
    dsimp only [e]
    exact (continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
      hd hdhalf lam u L M).norm.pow 2
  have hrightCont : Continuous (fun t : ℝ => 2 * C ^ 2 * (f t + e t)) :=
    continuous_const.mul (hfCont.add heCont)
  have hmono :
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2) ≤
      ∫ t in a..b, 2 * C ^ 2 * (f t + e t) :=
    intervalIntegral.integral_mono_on hab
      (hheadCont.intervalIntegrable (μ := MeasureTheory.volume) a b)
      (hrightCont.intervalIntegrable (μ := MeasureTheory.volume) a b) hpoint
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    (hfCont.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (heCont.intervalIntegrable (μ := MeasureTheory.volume) a b)]
  have hfBound :=
    integral_smoothAFEZetaDisplacedReflectedCombined_mollified_normSq_le
      (lam := lam) hd.le (logDeriv zetaChi (displacedLinePt d u)) L M hM hab
  change (∫ t in a..b, f t) ≤
      ‖((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d
          (logDeriv zetaChi (displacedLinePt d u)) L M‖ +
      smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam
        (logDeriv zetaChi (displacedLinePt d u)) L M at hfBound
  have heBound :=
    integral_smoothAFEZetaDisplacedReflectedCombinedFreezingError_normSq_le_dyadic
      (lam := lam) hd hdquarter hT huT hab huab hwidth hH L M hM
  change (∫ t in a..b, e t) ≤ D ^ 2 *
      (‖((b - a : ℝ) : ℂ) *
          smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
        smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M) at heBound
  have hsum := add_le_add hfBound heBound
  have hfactor0 : 0 ≤ 2 * C ^ 2 := by positivity
  change (2 * C ^ 2) * ((∫ t in a..b, f t) + ∫ t in a..b, e t) ≤ _
  change (2 * C ^ 2) * ((∫ t in a..b, f t) + ∫ t in a..b, e t) ≤
    (2 * C ^ 2) *
      ((‖((b - a : ℝ) : ℂ) *
          smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d
            (logDeriv zetaChi (displacedLinePt d u)) L M‖ +
        smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam
          (logDeriv zetaChi (displacedLinePt d u)) L M) +
      D ^ 2 *
        (‖((b - a : ℝ) : ℂ) *
            smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
          smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M))
  exact mul_le_mul_of_nonneg_left hsum hfactor0

end RHTower
