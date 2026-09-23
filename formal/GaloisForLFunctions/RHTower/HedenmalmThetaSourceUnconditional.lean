import GaloisForLFunctions.RHTower.HedenmalmHilbertSchmidtNorm
import GaloisForLFunctions.RHTower.HedenmalmIntervalAnomaly
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow
import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic

/-!
# The theta-cusp source as a positive density source

The whole quantile layer is developed for an abstract positive density source.  This module
supplies the actual arithmetic instance: the all-integer theta-cusp state

`k(x) = ∑_{n ≥ 1} e^{x/2} (4π² n⁴ e^{4x} - 6π n² e^{2x}) e^{-π n² e^{2x}}`

is continuous, everywhere strictly positive, and integrable, so it is a positive density source.
Its completed transform is the completed Riemann function `Ξ_C` on the strip `|Im z| < 1`, and the
tail condition of the quantile layer holds exactly there.

Every theorem of the quantile layer therefore specializes to a statement about the Riemann source
carrying no hypothesis on the source at all.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmHilbertSchmidt

/-! ### Global positivity -/

/-- **The theta-cusp source is everywhere strictly positive.**  Positivity on the positive
half-line is termwise; the negative half-line follows from the reflection law, and the seam point
is the separate cold-seam computation. -/
theorem thetaCuspFullSource_pos (x : ℝ) : 0 < thetaCuspFullSource x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : 0 < -x := by linarith
    have h := thetaCuspFullSource_pos_of_pos hy
    rwa [thetaCuspFullSource_neg x] at h
  · rw [hx]
    exact thetaCuspFullSource_zero_pos_for_cold_seam
  · exact thetaCuspFullSource_pos_of_pos hx

/-! ### The instance -/

/-- **The Hedenmalm theta source.**  The all-integer theta-cusp state as a positive density
source. -/
def thetaSource : PositiveDensitySource where
  k := thetaCuspFullSource
  continuous_k := contDiff_thetaCuspFullSource.continuous
  pos_k := thetaCuspFullSource_pos
  integrable_k := by
    refine (thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))).congr ?_
    filter_upwards with x
    exact thetaCuspSchwartzReal_apply x

@[simp] theorem thetaSource_k (x : ℝ) : thetaSource.k x = thetaCuspFullSource x := rfl

/-- **The theta source is even.** -/
theorem thetaSource_even (x : ℝ) : thetaSource.k (-x) = thetaSource.k x :=
  thetaCuspFullSource_neg x

/-! ### The exact strip of convergence -/

theorem thetaCuspDerivativeExpConstant_nonneg (m : ℕ) :
    0 ≤ thetaCuspDerivativeExpConstant m := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs m 0
  have hexp : Real.exp (-|(0 : ℝ)|) = 1 := by simp
  rw [hexp, mul_one] at h
  exact le_trans (abs_nonneg _) h

/-- **Exponential decay of the theta source.** -/
theorem abs_thetaCuspFullSource_le (x : ℝ) :
    |thetaCuspFullSource x| ≤ thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  rwa [iteratedDeriv_zero] at h

/-- **The tail condition of the quantile layer holds on the whole strip `|Im z| < 1`.** -/
theorem hasShiftedTail_thetaSource {z : ℂ} (hz : |z.im| < 1) : HasShiftedTail thetaSource z := by
  have hcpos : 0 < 1 - |z.im| := by linarith
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hcpos).const_mul (thetaCuspDerivativeExpConstant 0)) ?_ ?_
  · refine (contDiff_thetaCuspFullSource.continuous.mul ?_).aestronglyMeasurable
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  · filter_upwards with x
    have hbound := abs_thetaCuspFullSource_le x
    have hkey : Real.exp (-z.im * x) ≤ Real.exp (|z.im| * |x|) := by
      refine Real.exp_le_exp.mpr ?_
      calc -z.im * x ≤ |(-z.im) * x| := le_abs_self _
        _ = |z.im| * |x| := by rw [abs_mul, abs_neg]
    have hCnn := thetaCuspDerivativeExpConstant_nonneg 0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |thetaCuspFullSource x| * Real.exp (-z.im * x)
        ≤ (thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|)) * Real.exp (|z.im| * |x|) := by
          gcongr
      _ = thetaCuspDerivativeExpConstant 0 * Real.exp (-((1 - |z.im|) * |x|)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-! ### The completed transform is the completed Riemann function -/

/-- **The source transform of the theta source is `Ξ_C`** on the strip `|Im z| < 1`. -/
theorem xiC_thetaSource {z : ℂ} (hz : |z.im| < 1) : xiC thetaSource z = XiC z := by
  have hstrip : (-z) ∈ thetaCuspFourierLaplaceStrip := by
    have := abs_lt.mp hz
    exact ⟨by simpa using by linarith [this.2], by simpa using by linarith [this.1]⟩
  have hFL := thetaCuspFourierLaplace_eq_XiC_on_strip hstrip
  have hrw : xiC thetaSource z = thetaCuspFourierLaplace (-z) := by
    rw [xiC, thetaCuspFourierLaplace]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [thetaCuspFourierLaplaceIntegrand, sourceChar, thetaSource_k]
    rw [mul_comm]
    congr 2
    ring
  rw [hrw, hFL, XiC_even]


/-! ### Uniform bound and decay -/

/-- The uniform bound of the theta source. -/
def thetaBound : ℝ := thetaCuspDerivativeExpConstant 0

theorem thetaBound_nonneg : 0 ≤ thetaBound := thetaCuspDerivativeExpConstant_nonneg 0

/-- **The theta source is uniformly bounded.** -/
theorem thetaSource_le (x : ℝ) : thetaSource.k x ≤ thetaBound := by
  have h := abs_thetaCuspFullSource_le x
  have h1 : Real.exp (-|x|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp
  calc thetaSource.k x ≤ |thetaCuspFullSource x| := le_abs_self _
    _ ≤ thetaBound * Real.exp (-|x|) := h
    _ ≤ thetaBound * 1 := by gcongr; exact thetaBound_nonneg
    _ = thetaBound := mul_one _

/-- **The theta source vanishes at both ends of the line.** -/
theorem tendsto_thetaSource_atBot : Tendsto thetaSource.k atBot (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => -|x|) atBot atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atBot_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-|x|)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp habs
  have hbd : Tendsto (fun x : ℝ => thetaBound * Real.exp (-|x|)) atBot (𝓝 0) := by
    simpa using hexp.const_mul thetaBound
  refine squeeze_zero_norm (fun x => ?_) hbd
  simpa [thetaBound, Real.norm_eq_abs] using abs_thetaCuspFullSource_le x

theorem tendsto_thetaSource_atTop : Tendsto thetaSource.k atTop (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => -|x|) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atTop_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-|x|)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp habs
  have hbd : Tendsto (fun x : ℝ => thetaBound * Real.exp (-|x|)) atTop (𝓝 0) := by
    simpa using hexp.const_mul thetaBound
  refine squeeze_zero_norm (fun x => ?_) hbd
  simpa [thetaBound, Real.norm_eq_abs] using abs_thetaCuspFullSource_le x

/-! ### The canonical metric of the Riemann source -/

theorem norm_metricSymbol_thetaSource_le (t : ℝ) :
    ‖metricSymbol thetaSource t‖ ≤ thetaBound / thetaSource.mass :=
  norm_metricSymbol_le thetaSource thetaSource_le t

theorem thetaMetricBound_nonneg : 0 ≤ thetaBound / thetaSource.mass :=
  div_nonneg thetaBound_nonneg thetaSource.mass_pos.le

/-- **The canonical singular metric of the Riemann source.** -/
def thetaMetricOperator : Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le

/-- **The metric of the Riemann source has dense range** — unconditionally. -/
theorem denseRange_thetaMetricOperator : DenseRange thetaMetricOperator :=
  metricOperator_denseRange thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le

/-- **The metric of the Riemann source is not bounded below** — unconditionally.  Its inverse is
the genuinely singular direction of the quantile normal form. -/
theorem not_boundedBelow_thetaMetricOperator :
    ¬ ∃ ε : ℝ, 0 < ε ∧
      ∀ f : Lp ℂ 2 unitIntervalMeasure, ε * ‖f‖ ≤ ‖thetaMetricOperator f‖ :=
  not_boundedBelow_metricOperator thetaSource tendsto_thetaSource_atBot
    thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le

/-- **The metric pairing in quantile coordinates**, unconditionally. -/
theorem inner_thetaMetricOperator_quantileUnitary (f : SourceSpace thetaSource) :
    (inner ℂ (thetaMetricOperator (quantileUnitary thetaSource f))
      (quantileUnitary thetaSource f) : ℂ)
      = (((∫ x, ‖(f x : ℂ)‖ ^ (2 : ℕ)) / thetaSource.mass : ℝ) : ℂ) :=
  inner_metricOperator_quantileUnitary thetaSource thetaMetricBound_nonneg
    norm_metricSymbol_thetaSource_le f

/-! ### Unconditional forms of the source laws -/

open HedenmalmFredholmRange

/-- **The reflection law of the Riemann source inverse**, unconditionally: `R B R = -B`. -/
theorem sourceInverse_sourceReflection_theta {f : ℝ → ℂ}
    (hf : Integrable f (volume : Measure ℝ)) (x : ℝ) :
    sourceInverse thetaSource (sourceReflection f) (-x)
      = -sourceInverse thetaSource f x :=
  HedenmalmHilbertSchmidt.sourceInverse_sourceReflection thetaSource thetaSource_even hf x

/-- **The exact Fredholm alternative for the Riemann source.**  A two-ended solution of the
Hedenmalm source equation exists only at a zero of the completed Riemann function. -/
theorem XiC_eq_zero_of_solution {α : ℂ} (hα : |α.im| < 1) {u u' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (heq : ∀ x, -Complex.I * u' x + α * u x = -Complex.I * (thetaCuspFullSource x : ℂ))
    (hbot : Tendsto (fun x => u x * sourceChar α x) atBot (𝓝 0))
    (htop : Tendsto (fun x => u x * sourceChar α x) atTop (𝓝 0)) :
    XiC α = 0 := by
  have h := xiC_eq_zero_of_solution thetaSource hderiv heq (hasShiftedTail_thetaSource hα)
    hbot htop
  rwa [xiC_thetaSource hα] at h

/-- **The two formulas of the two-ended solution agree exactly at a zero of `Ξ_C`.** -/
theorem sourceModeI_eq_neg_tail_iff_XiC {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    sourceModeI thetaSource α x
      = -∫ y in Ioi x, (thetaCuspFullSource y : ℂ) * sourceChar α y ↔ XiC α = 0 := by
  have h := sourceModeI_eq_neg_tail_iff thetaSource (hasShiftedTail_thetaSource hα) x
  rw [xiC_thetaSource hα] at h
  exact h

/-- **The reflection law for the source modes of the Riemann source**, unconditionally. -/
theorem sourceModeI_neg_theta {z : ℂ} (hz : |z.im| < 1) (x : ℝ) :
    sourceModeI thetaSource (-z) (-x)
      = XiC z - sourceModeI thetaSource z x := by
  have h := sourceModeI_neg thetaSource thetaSource_even (hasShiftedTail_thetaSource hz) x
  rwa [xiC_thetaSource hz] at h

/-! ### Unconditional forms of the interval laws -/

open HedenmalmIntervalAnomaly

/-- **The reflection law of the theta interval mass**, unconditionally. -/
theorem intervalMass_neg_theta {a b : ℝ} (hab : a ≤ b) :
    intervalMass thetaSource (-b) (-a) = intervalMass thetaSource a b :=
  intervalMass_neg thetaSource thetaSource_even hab

/-- **The centered two-prime window of the Riemann source is reflection invariant.** -/
theorem centeredWindow_neg_theta {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow thetaSource n (-x) = centeredWindow thetaSource n x :=
  centeredWindow_neg thetaSource thetaSource_even hn x

end HedenmalmThetaSource

end

end RHTower
