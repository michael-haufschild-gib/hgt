import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFrozenCrossSubinterval
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedEnergyUpper
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedMovingMeanSquare
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# Moving reflected cross from frozen cross

The actual moving logarithmic chi slope is split exactly from its frozen value.  Its remaining
chi-weighted error is controlled on short dyadic subintervals by the direct energy and the proved
coefficient-freezing energy.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Chi-weighted error left after freezing the logarithmic chi slope at `u`. -/
def smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
    (lam d u : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) *
    smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M t

theorem continuous_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam u : ℝ) (L M : ℕ) :
    Continuous (smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M) := by
  exact (continuous_zetaChi_displacedLinePt hd hdhalf).mul
    (continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
      hd hdhalf lam u L M)

/-- Exact pointwise freezing split of the actual moving reflected head. -/
theorem smoothAFEZetaDisplacedReflectedMovingHead_eq_frozen_add_error
    (lam d u : ℝ) (L M : ℕ) (t : ℝ) :
    smoothAFEZetaDisplacedReflectedMovingHead lam d L M t =
      smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d
          (logDeriv zetaChi (displacedLinePt d u)) L M t +
        smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M t := by
  rw [smoothAFEZetaDisplacedReflectedMovingHead,
    smoothAFEZetaDisplacedReflectedMovingCarrier_eq_frozen_add_error]
  unfold smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead
  unfold smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
  ring

/-- Exact integrated split of the moving differentiated AFE cross. -/
theorem integral_conj_smoothAFEZetaDisplacedDirect_mul_movingReflected_eq_frozen_add_error
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x u : ℝ) (L M : ℕ) (a b : ℝ) :
    (∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedMovingHead lam d L M t) =
      (∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d
            (logDeriv zetaChi (displacedLinePt d u)) L M t) +
      (∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M t) := by
  let D : ℝ → ℂ := smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  let F : ℝ → ℂ := smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d
    (logDeriv zetaChi (displacedLinePt d u)) L M
  let E : ℝ → ℂ := smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M
  have hD : Continuous D :=
    continuous_smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  have hF : Continuous F := by
    exact (continuous_zetaChi_displacedLinePt hd hdhalf).mul
      ((Sieve.continuous_dirPoly L
        (fun n => smoothAFEZetaDisplacedReflectedCombinedCoeff lam d
          (logDeriv zetaChi (displacedLinePt d u)) n)).mul
        (continuous_levinsonLinearMollifier M))
  have hE : Continuous E :=
    continuous_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
      hd hdhalf lam u L M
  rw [intervalIntegral.integral_congr (fun t _ => by
    rw [smoothAFEZetaDisplacedReflectedMovingHead_eq_frozen_add_error
      lam d u L M t])]
  change (∫ t in a..b, (starRingEnd ℂ) (D t) * (F t + E t)) =
    (∫ t in a..b, (starRingEnd ℂ) (D t) * F t) +
      ∫ t in a..b, (starRingEnd ℂ) (D t) * E t
  have hdistrib :
      (fun t : ℝ => (starRingEnd ℂ) (D t) * (F t + E t)) =
        fun t : ℝ => (starRingEnd ℂ) (D t) * F t +
          (starRingEnd ℂ) (D t) * E t := by
    funext t
    ring
  rw [hdistrib]
  exact intervalIntegral.integral_add
    ((hD.star.mul hF).intervalIntegrable (μ := MeasureTheory.volume) a b)
    ((hD.star.mul hE).intervalIntegrable (μ := MeasureTheory.volume) a b)

/-- Cauchy--Schwarz bound for the cross with the chi-weighted freezing error. -/
theorem norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_freezingError_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hab : a ≤ b) (lam x u : ℝ) (L M : ℕ) :
    ‖∫ t in a..b,
        (starRingEnd ℂ)
            (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M t‖ ≤
      Real.sqrt (∫ t in a..b,
          ‖smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t‖ ^ 2) *
        Real.sqrt (∫ t in a..b,
          ‖smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
            lam d u L M t‖ ^ 2) := by
  let D : ℝ → ℂ := smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  let E : ℝ → ℂ := smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M
  have hD : Continuous D :=
    continuous_smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  have hE : Continuous E :=
    continuous_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
      hd hdhalf lam u L M
  calc
    ‖∫ t in a..b, (starRingEnd ℂ) (D t) * E t‖
        ≤ ∫ t in a..b, ‖(starRingEnd ℂ) (D t) * E t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, ‖D t‖ * ‖E t‖ := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ‖(starRingEnd ℂ) (D t) * E t‖ = ‖D t‖ * ‖E t‖
      rw [norm_mul]
      have hs : ‖(starRingEnd ℂ) (D t)‖ = ‖D t‖ := by
        change ‖star (D t)‖ = ‖D t‖
        exact norm_star (D t)
      rw [hs]
    _ ≤ Real.sqrt (∫ t in a..b, ‖D t‖ ^ 2) *
          Real.sqrt (∫ t in a..b, ‖E t‖ ^ 2) :=
      GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_le_sqrt_mul_sqrt hD hE hab

/-- The chi-weighted freezing-error energy inherits the uniform left-line chi envelope. -/
theorem exists_integral_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError_normSq_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℝ), 0 < d → d ≤ d₀ → d ≤ 1 / 4 →
      ∀ (lam T u H a b : ℝ) (L M : ℕ),
        4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
        u ∈ Set.Icc a b → b - a ≤ H → 2 * H ≤ T → 1 < M →
        (∫ t in a..b,
          ‖smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
            lam d u L M t‖ ^ 2) ≤
          (K * (2 * T) ^ d) ^ 2 *
            ((|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
              (‖((b - a : ℝ) : ℂ) *
                  smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
                smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M)) := by
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_displacedLinePt_le_dyadic hd₀0 hd₀half
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ hdquarter lam T u H a b L M hT haT hab hbT huab hwidth hH hM
  let C : ℝ := K * (2 * T) ^ d
  let E : ℝ → ℂ :=
    smoothAFEZetaDisplacedReflectedCombinedFreezingError lam d u L M
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  have hweightedCont :=
    continuous_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
      hd hdhalf lam u L M
  have hECont :=
    continuous_smoothAFEZetaDisplacedReflectedCombinedFreezingError
      hd hdhalf lam u L M
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖smoothAFEZetaDisplacedReflectedChiWeightedFreezingError lam d u L M t‖ ^ 2 ≤
        C ^ 2 * ‖E t‖ ^ 2 := by
    intro t ht
    have htT : t ∈ Set.Icc T (2 * T) := ⟨haT.trans ht.1, ht.2.trans hbT⟩
    have hz := hchi d hd.le hdd₀ T t (by linarith) htT
    change ‖zetaChi (displacedLinePt d t)‖ ≤ C at hz
    change ‖zetaChi (displacedLinePt d t) * E t‖ ^ 2 ≤ C ^ 2 * ‖E t‖ ^ 2
    rw [norm_mul]
    have hsquare : ‖zetaChi (displacedLinePt d t)‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [norm_nonneg (zetaChi (displacedLinePt d t))]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg ‖E t‖)
  have hmono :
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
          lam d u L M t‖ ^ 2) ≤
        ∫ t in a..b, C ^ 2 * ‖E t‖ ^ 2 := by
    exact intervalIntegral.integral_mono_on hab
      ((hweightedCont.norm.pow 2).intervalIntegrable a b)
      ((continuous_const.mul (hECont.norm.pow 2)).intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  have hfreeze :=
    integral_smoothAFEZetaDisplacedReflectedCombinedFreezingError_normSq_le_dyadic
      (lam := lam) hd hdquarter hT ⟨haT.trans huab.1, huab.2.trans hbT⟩
        hab huab hwidth hH L M hM
  change C ^ 2 * (∫ t in a..b, ‖E t‖ ^ 2) ≤ C ^ 2 *
    ((|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
      (‖((b - a : ℝ) : ℂ) *
          smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
        smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M))
  exact mul_le_mul_of_nonneg_left hfreeze (sq_nonneg C)

/-- Explicit short-window bound for the direct cross with the chi-weighted freezing error. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_freezingError_le_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℝ), 0 < d → d ≤ d₀ → d ≤ 1 / 4 →
      ∀ (lam x T u H a b : ℝ) (L M : ℕ),
        4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
        u ∈ Set.Icc a b → b - a ≤ H → 2 * H ≤ T → 1 < M →
        ‖∫ t in a..b,
            (starRingEnd ℂ)
                (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
              smoothAFEZetaDisplacedReflectedChiWeightedFreezingError
                lam d u L M t‖ ≤
          Real.sqrt
              (((b - a) + 8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M))) *
                ∑ r : Fin (L * M),
                  ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ 2) *
            Real.sqrt
              ((K * (2 * T) ^ d) ^ 2 *
                ((|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
                  (‖((b - a : ℝ) : ℂ) *
                      smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
                    smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M))) := by
  obtain ⟨K, hK, herror⟩ :=
    exists_integral_smoothAFEZetaDisplacedReflectedChiWeightedFreezingError_normSq_le_dyadic
      hd₀0 hd₀half
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ hdquarter lam x T u H a b L M hT haT hab hbT huab hwidth hH hM
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  have hcs := norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_freezingError_le
    hd hdhalf hab lam x u L M
  have hdirect := integral_normSq_smoothAFEZetaDisplacedMollifiedDirectHead_le
    lam d x L M a b
  have herr := herror d hd hdd₀ hdquarter lam T u H a b L M
    hT haT hab hbT huab hwidth hH hM
  refine hcs.trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hdirect) (Real.sqrt_le_sqrt herr)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Actual moving differentiated AFE cross equals its frozen oscillatory cross up to the explicit
short-window coefficient-freezing error. -/
theorem exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_movingReflected_le_frozen_add_dyadic
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℝ), 0 < d → d ≤ d₀ → d ≤ 1 / 4 →
      ∀ (lam x T u H a b : ℝ) (L M : ℕ),
        4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
        u ∈ Set.Icc a b → b - a ≤ H → 2 * H ≤ T → 1 < M →
        ‖∫ t in a..b,
            (starRingEnd ℂ)
                (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
              smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ≤
          ‖∫ t in a..b,
            (starRingEnd ℂ)
                (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
              smoothAFEZetaDisplacedReflectedChiWeightedFrozenHead lam d
                (logDeriv zetaChi (displacedLinePt d u)) L M t‖ +
          Real.sqrt
              (((b - a) + 8 * ((L * M : ℕ) : ℝ) * (1 + Real.log (L * M))) *
                ∑ r : Fin (L * M),
                  ‖smoothAFEZetaDisplacedDirectMollifiedCoeff lam d x L M r‖ ^ 2) *
            Real.sqrt
              ((K * (2 * T) ^ d) ^ 2 *
                ((|lam| * ((8 + 4 * Real.pi) * (1 + H) / T)) ^ 2 *
                  (‖((b - a : ℝ) : ℂ) *
                      smoothAFEZetaDisplacedReflectedBaseMollifiedDiagonal d L M‖ +
                    smoothAFEZetaDisplacedReflectedBaseMollifiedMeanError L M))) := by
  obtain ⟨K, hK, herror⟩ :=
    exists_norm_integral_conj_smoothAFEZetaDisplacedDirect_mul_freezingError_le_dyadic
      hd₀0 hd₀half
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ hdquarter lam x T u H a b L M hT haT hab hbT huab hwidth hH hM
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  have hsplit :=
    integral_conj_smoothAFEZetaDisplacedDirect_mul_movingReflected_eq_frozen_add_error
      hd hdhalf lam x u L M a b
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  exact add_le_add (le_refl _)
    (herror d hd hdd₀ hdquarter lam x T u H a b L M
      hT haT hab hbT huab hwidth hH hM)

end

end RHTower
