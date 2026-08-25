import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedCombinedEnergyUpper
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine

/-!
# Chi-weighted frozen reflected mean square

Uniform left-line conductor growth is transferred to the exact frozen combined reflected
mollified mean value on a dyadic block.  The gcd-reduced diagonal is retained verbatim.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Literal chi-weighted frozen combined reflected head. -/
def smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead
    (lam d : ℝ) (q : ℂ) (L M : ℕ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) *
    (Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t *
      Sieve.levinsonLinearMollifier M t)

/-- One constant gives the conductor-growth envelope on every displaced dyadic line in a fixed
compact displacement range. -/
theorem exists_norm_zetaChi_displacedLinePt_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 ≤ d → d ≤ d₀ →
      ∀ T t : ℝ, 1 ≤ T → t ∈ Set.Icc T (2 * T) →
        ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d := by
  obtain ⟨K, hK, hglobal⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow hd₀0 hd₀half
  refine ⟨K, hK, fun d hd hdd₀ T t hT ht => ?_⟩
  have hz := hglobal d hd hdd₀ t
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hmax : max 1 |t| ≤ 2 * T := by
    rw [abs_of_nonneg ht0]
    exact max_le (by linarith) ht.2
  have hrpow : (max 1 |t|) ^ d ≤ (2 * T) ^ d :=
    Real.rpow_le_rpow (by positivity) hmax hd
  simpa only [displacedLinePt] using
    hz.trans (mul_le_mul_of_nonneg_left hrpow hK)

/-- Pointwise chi-weighted frozen-head bound on a dyadic block. -/
theorem norm_smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead_le_dyadic
    {K lam d T t : ℝ}
    (hchi : ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d)
    (q : ℂ) (L M : ℕ) :
    ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ≤
      (K * (2 * T) ^ d) *
        (‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖) := by
  rw [smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hchi
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Uniform chi-weighted frozen reflected energy on every subinterval of a dyadic block.  The
constant is supplied unconditionally by the proved uniform left-line chi estimate. -/
theorem exists_integral_smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead_normSq_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℝ), 0 < d → d ≤ d₀ →
      ∀ (lam T a b : ℝ) (q : ℂ) (L M : ℕ),
        1 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T → 1 < M →
        (∫ t in a..b,
          ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead
              lam d q L M t‖ ^ 2) ≤
          (K * (2 * T) ^ d) ^ 2 *
            (‖((b - a : ℝ) : ℂ) *
                smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal
                  lam d q L M‖ +
              smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError
                lam q L M) := by
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_displacedLinePt_le_dyadic hd₀0 hd₀half
  refine ⟨K, hK, fun d hd hdd₀ lam T a b q L M hT haT hab hbT hM => ?_⟩
  let C : ℝ := K * (2 * T) ^ d
  let g : ℝ → ℝ := fun t =>
    (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ^ 2 ≤
        C ^ 2 * g t := by
    intro t ht
    have htT : t ∈ Set.Icc T (2 * T) := ⟨haT.trans ht.1, ht.2.trans hbT⟩
    have hz := hchi d hd.le hdd₀ T t hT htT
    have hnorm :=
      norm_smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead_le_dyadic
        (lam := lam) hz q L M
    have hbase0 : 0 ≤
        ‖Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    change ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ≤
      C * (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) at hnorm
    change ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ^ 2 ≤
      C ^ 2 * (‖Sieve.dirPoly L
          (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
        ‖Sieve.levinsonLinearMollifier M t‖) ^ 2
    nlinarith [norm_nonneg
      (smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t)]
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  have hchiCont := continuous_norm_zetaChi_left_line hd hdhalf
  have hdirCont :=
    (Sieve.continuous_dirPoly L
      (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n)).norm
  have hmollCont := (continuous_levinsonLinearMollifier M).norm
  have hintHead : IntervalIntegrable
      (fun t =>
        ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ^ 2)
      MeasureTheory.volume a b := by
    have heq :
        (fun t : ℝ =>
          ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ^ 2) =
        (fun t : ℝ =>
          (‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ *
            (‖Sieve.dirPoly L
                (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d q n) t‖ *
              ‖Sieve.levinsonLinearMollifier M t‖)) ^ 2) := by
      funext t
      simp [smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead,
        displacedLinePt]
    rw [heq]
    exact ((hchiCont.mul (hdirCont.mul hmollCont)).pow 2).intervalIntegrable a b
  have hcontG : Continuous g := by
    dsimp only [g]
    exact ((hdirCont.mul hmollCont).pow 2)
  have hmono :
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d q L M t‖ ^ 2) ≤
      ∫ t in a..b, C ^ 2 * g t := by
    have hcontRight : Continuous (fun t : ℝ => C ^ 2 * g t) :=
      continuous_const.mul hcontG
    exact intervalIntegral.integral_mono_on hab hintHead
      (hcontRight.intervalIntegrable (μ := MeasureTheory.volume) a b) hpoint
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hbase :=
    integral_smoothAFEZetaDisplacedReflectedCombined_mollified_normSq_le
      (lam := lam) hd.le q L M hM hab
  change (∫ t in a..b, g t) ≤
      ‖((b - a : ℝ) : ℂ) *
        smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ +
      smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam q L M at hbase
  change C ^ 2 * (∫ t in a..b, g t) ≤ _
  change C ^ 2 * (∫ t in a..b, g t) ≤ C ^ 2 *
      (‖((b - a : ℝ) : ℂ) *
          smoothAFEZetaDisplacedReflectedCombinedMollifiedDiagonal lam d q L M‖ +
        smoothAFEZetaDisplacedReflectedCombinedMollifiedMeanError lam q L M)
  exact mul_le_mul_of_nonneg_left hbase (sq_nonneg C)

end RHTower
