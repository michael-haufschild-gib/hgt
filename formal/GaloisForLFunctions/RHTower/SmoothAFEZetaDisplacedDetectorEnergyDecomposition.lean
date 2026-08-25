import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleRemainderMeanSquare
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Exact differentiated displaced detector energy decomposition

The full finite mollified detector is assembled as direct head, literal moving chi-weighted
reflected head, and Gaussian pole remainder.  Squared-energy identities retain the genuine
direct/reflected stationary cross term exactly.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Direct mollified detector head in its exact convolution-polynomial normal form. -/
def smoothAFEZetaDisplacedMollifiedDirectHead
    (lam d x : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  Sieve.dirPoly (L * M)
    (Sieve.dirConv L M
      (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
      (levinsonLinearMollifierFinCoeff M)) (-t)

/-- Direct plus moving reflected principal part, before Gaussian pole remainders. -/
def smoothAFEZetaDisplacedMollifiedPrincipalHead
    (lam d x : ℝ) (L M : ℕ) (t : ℝ) : ℂ :=
  smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t +
    smoothAFEZetaDisplacedReflectedMovingHead lam d L M t

/-- Exact assembly of the full finite mollified detector into the two principal heads and pole
remainder. -/
theorem smoothAFEZetaDisplacedFiniteClassicalDetector_mul_mollifier_eq_principal_add_pole
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x t : ℝ) (L M : ℕ) :
    smoothAFEZetaDisplacedFiniteClassicalDetector lam d x t L *
        Sieve.levinsonLinearMollifier M t =
      smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M t +
        smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t := by
  rw [smoothAFEZetaDisplacedFiniteClassicalDetector_mul_levinsonLinearMollifier_eq_combined
    hd hdhalf]
  unfold smoothAFEZetaDisplacedMollifiedPrincipalHead
  unfold smoothAFEZetaDisplacedMollifiedDirectHead
  unfold smoothAFEZetaDisplacedReflectedMovingHead
  unfold smoothAFEZetaDisplacedReflectedMovingCarrier
  unfold smoothAFEZetaDisplacedMollifiedPoleRemainder
  ring

theorem continuous_zetaChi_displacedLinePt
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    Continuous (fun t : ℝ => zetaChi (displacedLinePt d t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hgamma : Gammaℝ (1 - displacedLinePt d t) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith
  exact (zetaChi_analyticAt hgamma).continuousAt.comp
    (hasDerivAt_displacedLinePt d t).continuousAt

theorem continuous_smoothAFEZetaDisplacedMollifiedDirectHead
    (lam d x : ℝ) (L M : ℕ) :
    Continuous (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M) := by
  unfold smoothAFEZetaDisplacedMollifiedDirectHead
  exact (Sieve.continuous_dirPoly (L * M)
    (Sieve.dirConv L M
      (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
      (levinsonLinearMollifierFinCoeff M))).comp continuous_id.neg

theorem continuous_smoothAFEZetaDisplacedReflectedMovingHead
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam : ℝ) (L M : ℕ) :
    Continuous (smoothAFEZetaDisplacedReflectedMovingHead lam d L M) := by
  unfold smoothAFEZetaDisplacedReflectedMovingHead
  exact (continuous_zetaChi_displacedLinePt hd hdhalf).mul
    (continuous_smoothAFEZetaDisplacedReflectedMovingCarrier hd hdhalf lam L M)

theorem continuous_smoothAFEZetaDisplacedMollifiedPrincipalHead
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x : ℝ) (L M : ℕ) :
    Continuous (smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M) := by
  exact (continuous_smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M).add
    (continuous_smoothAFEZetaDisplacedReflectedMovingHead hd hdhalf lam L M)

/-- Pointwise principal energy with the direct/reflected cross retained exactly. -/
theorem normSq_smoothAFEZetaDisplacedMollifiedPrincipalHead_eq
    (lam d x : ℝ) (L M : ℕ) (t : ℝ) :
    ‖smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M t‖ ^ 2 =
      ‖smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t‖ ^ 2 +
      ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2 +
      2 * ((starRingEnd ℂ)
        (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
          smoothAFEZetaDisplacedReflectedMovingHead lam d L M t).re := by
  exact norm_add_sq_complex _ _

/-- Full detector energy with the pole cross retained exactly. -/
theorem normSq_smoothAFEZetaDisplacedFiniteClassicalDetector_mul_mollifier_eq
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x t : ℝ) (L M : ℕ) :
    ‖smoothAFEZetaDisplacedFiniteClassicalDetector lam d x t L *
        Sieve.levinsonLinearMollifier M t‖ ^ 2 =
      ‖smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M t‖ ^ 2 +
      ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ^ 2 +
      2 * ((starRingEnd ℂ)
        (smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M t) *
          smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t).re := by
  rw [smoothAFEZetaDisplacedFiniteClassicalDetector_mul_mollifier_eq_principal_add_pole
    hd hdhalf]
  exact norm_add_sq_complex _ _

/-- Integrated principal energy identity.  The only mixed principal contribution is the literal
direct/reflected cross integral. -/
theorem integral_normSq_smoothAFEZetaDisplacedMollifiedPrincipalHead_eq
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (lam x : ℝ) (L M : ℕ) (a b : ℝ) :
    (∫ t in a..b,
      ‖smoothAFEZetaDisplacedMollifiedPrincipalHead lam d x L M t‖ ^ 2) =
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t‖ ^ 2) +
      (∫ t in a..b,
        ‖smoothAFEZetaDisplacedReflectedMovingHead lam d L M t‖ ^ 2) +
      2 * (∫ t in a..b,
        ((starRingEnd ℂ)
          (smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M t) *
            smoothAFEZetaDisplacedReflectedMovingHead lam d L M t).re) := by
  let D : ℝ → ℂ := smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  let R : ℝ → ℂ := smoothAFEZetaDisplacedReflectedMovingHead lam d L M
  have hD : Continuous D :=
    continuous_smoothAFEZetaDisplacedMollifiedDirectHead lam d x L M
  have hR : Continuous R :=
    continuous_smoothAFEZetaDisplacedReflectedMovingHead hd hdhalf lam L M
  have hDsq : Continuous (fun t => ‖D t‖ ^ 2) := hD.norm.pow 2
  have hRsq : Continuous (fun t => ‖R t‖ ^ 2) := hR.norm.pow 2
  have hcross : Continuous (fun t => ((starRingEnd ℂ) (D t) * R t).re) := by
    fun_prop
  rw [intervalIntegral.integral_congr (fun t _ =>
    normSq_smoothAFEZetaDisplacedMollifiedPrincipalHead_eq lam d x L M t)]
  change (∫ t in a..b,
      (‖D t‖ ^ 2 + ‖R t‖ ^ 2) +
        (2 * ((starRingEnd ℂ) (D t) * R t).re)) =
    (∫ t in a..b, ‖D t‖ ^ 2) +
      (∫ t in a..b, ‖R t‖ ^ 2) +
      2 * (∫ t in a..b, ((starRingEnd ℂ) (D t) * R t).re)
  have hsplit :
      (∫ t in a..b,
        (‖D t‖ ^ 2 + ‖R t‖ ^ 2) +
          (2 * ((starRingEnd ℂ) (D t) * R t).re)) =
        (∫ t in a..b, ‖D t‖ ^ 2 + ‖R t‖ ^ 2) +
          (∫ t in a..b, 2 * ((starRingEnd ℂ) (D t) * R t).re) :=
    intervalIntegral.integral_add
      ((hDsq.add hRsq).intervalIntegrable (μ := MeasureTheory.volume) a b)
      ((continuous_const.mul hcross).intervalIntegrable
        (μ := MeasureTheory.volume) a b)
  rw [hsplit]
  rw [intervalIntegral.integral_add
    (hDsq.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (hRsq.intervalIntegrable (μ := MeasureTheory.volume) a b)]
  rw [intervalIntegral.integral_const_mul]

end RHTower
