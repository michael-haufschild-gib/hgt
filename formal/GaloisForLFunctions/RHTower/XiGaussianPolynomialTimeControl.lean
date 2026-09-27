import GaloisForLFunctions.RHTower.XiGaussianDebtDomination
import GaloisForLFunctions.HTGeometry.GaussianDegreeNormalizedSlope

/-!
# A common polynomial degree/time region for the actual Xi trace

The full phase-debt slope grows only polynomially with degree. Normalizing
spatial scale by (d+3)²√(d+3) gives one loss envelope for every degree and every
coefficient vector, while keeping the complete actual complex divisor energy.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Positive spatial scale with the polynomial degree loss removed. -/
def xiGaussianDegreeScale (d : ℕ) (τ : ℝ) : {r : ℝ // 0 < r} :=
  ⟨Real.exp τ / gaussianDegreeWeight d, div_pos (Real.exp_pos τ) (gaussianDegreeWeight_pos d)⟩

/-- One continuous envelope for all polynomial degrees and coefficient directions. -/
def xiGaussianUniformTraceLoss (C h u : ℝ) : ℝ :=
  C * u + (1 + 2 * h * Real.sqrt (4 * π) * u) * parabolicGaussianDefect (u / 2) ^ 2 +
    u * h * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
      (1 + 2 * Real.sqrt (4 * π)) * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2

/-- At the polynomial degree scale, every loss term has a degree-independent upper bound. -/
theorem xiGaussianTraceLoss_degreeScale_le (C h : ℝ≥0) (d : ℕ) (τ : ℝ) :
    xiGaussianTraceLoss C h d (xiGaussianDegreeScale d τ) ≤
      xiGaussianUniformTraceLoss C h (Real.exp τ) := by
  let u := Real.exp τ
  let r := xiGaussianDegreeScale d τ
  let A := Real.sqrt (4 * π)
  let v := Real.sqrt ((d : ℝ) + 3)
  let ε : ℝ≥0 := ⟨u / 2, (div_pos (Real.exp_pos τ) (by positivity)).le⟩
  have hu : 0 < u := Real.exp_pos τ
  have hr : 0 < (r : ℝ) := r.property
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hS : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have hrv : (r : ℝ) * v ≤ u := by
    change (u / gaussianDegreeWeight d) * v ≤ u
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (gaussianDegreeWeight_pos d)).mpr
      (mul_le_mul_of_nonneg_left (sqrt_le_gaussianDegreeWeight d) hu.le)
  have hsqrt₁ : Real.sqrt ((d : ℝ) + 1) ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hsqrt₂ : Real.sqrt ((d : ℝ) + 2) ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hr₁ := (mul_le_mul_of_nonneg_left hsqrt₁ hr.le).trans hrv
  have hr₂ := (mul_le_mul_of_nonneg_left hsqrt₂ hr.le).trans hrv
  have hfirst := mul_le_mul_of_nonneg_left hr₁ C.coe_nonneg
  have hfactor : 1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * π * ((d : ℝ) + 2)) ≤
      1 + 2 * (h : ℝ) * A * u := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    have hs := mul_le_mul_of_nonneg_left hr₂
      (show 0 ≤ 2 * (h : ℝ) * A by positivity)
    nlinarith only [hs]
  have hrad : (r : ℝ) / 2 = (ε : ℝ) / gaussianDegreeWeight d := by
    change (u / gaussianDegreeWeight d) / 2 = (u / 2) / gaussianDegreeWeight d
    ring
  have hE : verticalPolynomialGaussianDefect d ((r : ℝ) / 2) ≤ parabolicGaussianDefect (u / 2) := by
    rw [hrad]
    exact verticalPolynomialGaussianDefect_degreeWeight_le d ε
  have hEsq := pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg _ _) hE 2
  have herror := mul_le_mul hfactor hEsq (sq_nonneg _) (by positivity)
  have hT : gaussianCoordinateVerticalSlope d ((r : ℝ) / 2) ^ 2 ≤
      (1 + 2 * A) * gaussianDegreeWeight d * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2 := by
    rw [hrad]
    exact gaussianCoordinateVerticalSlope_degreeWeight_sq_le d ε
  have hdebt := mul_le_mul_of_nonneg_left hT
    (show 0 ≤ ((r : ℝ) * h) * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) by positivity)
  have hcancel : (r : ℝ) * gaussianDegreeWeight d = u :=
    div_mul_cancel₀ u (gaussianDegreeWeight_pos d).ne'
  have hid : ((r : ℝ) * h) * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
      ((1 + 2 * A) * gaussianDegreeWeight d * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2) =
      u * h * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
        (1 + 2 * A) * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2 := by
    calc
      _ = ((r : ℝ) * gaussianDegreeWeight d) * h *
          (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
            (1 + 2 * A) * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2 := by ring
      _ = _ := by rw [hcancel]
  rw [hid] at hdebt
  unfold xiGaussianTraceLoss xiGaussianSlopePhaseBudget xiGaussianUniformTraceLoss
  change C * (r : ℝ) * _ + _ + (r : ℝ) * h * _ ≤ C * u + _ + _
  nlinarith only [hfirst, herror, hdebt]

/-- The degree-independent complete trace-loss envelope vanishes at zero. -/
theorem xiGaussianUniformTraceLoss_tendsto_zero (C h : ℝ) :
    Tendsto (xiGaussianUniformTraceLoss C h) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (xiGaussianUniformTraceLoss C h) := by
    unfold xiGaussianUniformTraceLoss parabolicGaussianDefect
    have hJ := continuous_gaussianNormalizedSlopeEnvelope
    fun_prop
  simpa [xiGaussianUniformTraceLoss, parabolicGaussianDefect] using hc.tendsto 0

/-- One logarithmic cutoff controls the complete loss for every polynomial degree. -/
theorem eventually_forall_xiGaussianTraceLoss_degreeScale_lt (C h : ℝ≥0) :
    ∀ᶠ τ : ℝ in atBot, ∀ d : ℕ,
      xiGaussianTraceLoss C h d (xiGaussianDegreeScale d τ) < 1 / 8 := by
  have ht := (xiGaussianUniformTraceLoss_tendsto_zero C h).comp Real.tendsto_exp_atBot
  have he := ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 8))
  filter_upwards [he] with τ hτ d
  exact (xiGaussianTraceLoss_degreeScale_le C h d τ).trans_lt hτ

/-- The complete actual trace has one positive margin throughout a common polynomial degree region. -/
theorem exists_eventually_forall_xiGaussian_trace_degreeScale_floor :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ P : Polynomial ℝ,
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianDegreeScale (2 * P.natDegree) τ : ℝ) * h) *
        xiPolynomialGaussianHeatTraceReal
          (P.comp (Polynomial.C ((xiGaussianDegreeScale (2 * P.natDegree) τ : ℝ) ^ 2) * Polynomial.X))
          (2 * π * (xiGaussianDegreeScale (2 * P.natDegree) τ : ℝ) ^ 2) := by
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiGaussian_trace_slope_lower_bound
  refine ⟨h, hh, ?_⟩
  filter_upwards [eventually_forall_xiGaussianTraceLoss_degreeScale_lt
    (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)] with τ hτ P
  have hsmall : xiGaussianTraceLoss C h (2 * P.natDegree)
      (xiGaussianDegreeScale (2 * P.natDegree) τ) < 1 / 8 := hτ (2 * P.natDegree)
  have hm := mul_le_mul_of_nonneg_right
    (show (1 / 8 : ℝ) ≤ 1 / 4 - xiGaussianTraceLoss C h (2 * P.natDegree)
        (xiGaussianDegreeScale (2 * P.natDegree) τ) by linarith only [hsmall])
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  exact hm.trans (hfloor P _)

end RHTower
