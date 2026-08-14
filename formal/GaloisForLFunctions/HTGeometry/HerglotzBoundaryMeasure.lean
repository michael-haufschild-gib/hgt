import GaloisForLFunctions.HTGeometry.HerglotzDiscDilation
import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation

/-!
# The boundary probability family of a Carathéodory germ

Dilating a holomorphic function with nonnegative real part and value one at the centre produces, for
each radius below one, a probability density on the circle.  This file builds that family as genuine
probability measures; its weak-* limit points are the Herglotz measures of the germ.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Metric
open scoped ENNReal

noncomputable section

/-- The boundary density of a germ at radius `r`. -/
def herglotzDensity (F : ℂ → ℂ) (r : ℝ) (ζ : Circle) : ℝ≥0∞ :=
  ENNReal.ofReal ((F ((r : ℂ) * (ζ : ℂ))).re)

/-- The boundary density measure of a germ at radius `r`. -/
def herglotzBoundaryMeasure (F : ℂ → ℂ) (r : ℝ) : Measure Circle :=
  circleLebesgue.withDensity (herglotzDensity F r)

theorem continuous_dilate_circle {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    Continuous fun ζ : Circle => F ((r : ℂ) * (ζ : ℂ)) := by
  have hmaps : ∀ ζ : Circle, ((r : ℂ) * (ζ : ℂ)) ∈ ball (0 : ℂ) 1 := by
    intro ζ
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, Circle.norm_coe, mul_one]
    exact hr1
  have hcont : ContinuousOn F (ball (0 : ℂ) 1) := hF.continuousOn
  refine (hcont.comp_continuous ?_ hmaps)
  fun_prop

theorem integrable_dilate_circle {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    Integrable (fun ζ : Circle => ((F ((r : ℂ) * (ζ : ℂ))).re)) circleLebesgue := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact Complex.continuous_re.comp (continuous_dilate_circle hr0 hr1 hF)
  · exact HasCompactSupport.of_compactSpace _

/-- **The dilated boundary mass is the value at the centre.** -/
theorem integral_re_dilate_circle {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    ∫ ζ : Circle, ((F ((r : ℂ) * (ζ : ℂ))).re) ∂circleLebesgue = (F 0).re := by
  have hmeas : AEStronglyMeasurable (fun ζ : Circle => F ((r : ℂ) * (ζ : ℂ))) circleLebesgue :=
    (continuous_dilate_circle hr0 hr1 hF).aestronglyMeasurable
  have hcomplex := integral_circleLebesgue_eq_circleAverage_complex
    (fun z => F ((r : ℂ) * z)) hmeas
  rw [circleAverage_dilate_eq_center hr0 hr1 hF] at hcomplex
  have hInt : Integrable (fun ζ : Circle => F ((r : ℂ) * (ζ : ℂ))) circleLebesgue :=
    (continuous_dilate_circle hr0 hr1 hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫ ζ : Circle, ((F ((r : ℂ) * (ζ : ℂ))).re) ∂circleLebesgue
      = (∫ ζ : Circle, F ((r : ℂ) * (ζ : ℂ)) ∂circleLebesgue).re := by
        simpa using Complex.reCLM.integral_comp_comm hInt
    _ = (F 0).re := by rw [hcomplex]

/-- **The boundary family consists of probability measures.** -/
theorem isProbabilityMeasure_herglotzBoundaryMeasure {F : ℂ → ℂ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re) (h1 : F 0 = 1) :
    IsProbabilityMeasure (herglotzBoundaryMeasure F r) := by
  constructor
  have hnn : 0 ≤ᵐ[circleLebesgue] fun ζ : Circle => ((F ((r : ℂ) * (ζ : ℂ))).re) := by
    refine Filter.Eventually.of_forall fun ζ => ?_
    refine hpos _ ?_
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, Circle.norm_coe, mul_one]
    exact hr1
  have hint := integrable_dilate_circle hr0 hr1 hF
  have hlint : ∫⁻ ζ : Circle, ENNReal.ofReal ((F ((r : ℂ) * (ζ : ℂ))).re) ∂circleLebesgue
      = ENNReal.ofReal (∫ ζ : Circle, ((F ((r : ℂ) * (ζ : ℂ))).re) ∂circleLebesgue) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  rw [herglotzBoundaryMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [show (∫⁻ ζ : Circle, herglotzDensity F r ζ ∂circleLebesgue)
      = ∫⁻ ζ : Circle, ENNReal.ofReal ((F ((r : ℂ) * (ζ : ℂ))).re) ∂circleLebesgue from rfl]
  rw [hlint, integral_re_dilate_circle hr0 hr1 hF, h1]
  simp

/-- **The Poisson representation over the circle measure.**  Integrating the Poisson kernel against
the boundary density at radius `r` returns the real part of the dilated germ. -/
theorem integral_poissonKernel_density {F : ℂ → ℂ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∫ ζ : Circle, (_root_.poissonKernel 0 w (ζ : ℂ)) * ((F ((r : ℂ) * (ζ : ℂ))).re)
        ∂circleLebesgue
      = (F ((r : ℂ) * w)).re := by
  classical
  have hdilcont : Continuous fun ζ : Circle => F ((r : ℂ) * (ζ : ℂ)) :=
    continuous_dilate_circle hr0 hr1 hF
  have hne : ∀ ζ : Circle, ((ζ : ℂ) - 0) - (w - 0) ≠ 0 := by
    intro ζ h
    have hzw : (ζ : ℂ) = w := by
      have := sub_eq_zero.mp h
      simpa using this
    rw [mem_ball, dist_zero_right] at hw
    have hnorm : ‖(ζ : ℂ)‖ = 1 := Circle.norm_coe ζ
    rw [hzw] at hnorm
    rw [hnorm] at hw
    exact absurd hw (lt_irrefl 1)
  have hPcont : Continuous fun ζ : Circle => _root_.poissonKernel 0 w (ζ : ℂ) := by
    unfold _root_.poissonKernel
    have hden : ∀ ζ : Circle, ‖((ζ : ℂ) - 0) - (w - 0)‖ ^ 2 ≠ 0 := fun ζ =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne ζ))
    fun_prop (disch := exact hden _)
  have hmeas : AEStronglyMeasurable
      (fun z : Circle => ((_root_.poissonKernel 0 w (z : ℂ) : ℂ) * F ((r : ℂ) * (z : ℂ))))
      circleLebesgue :=
    ((Complex.continuous_ofReal.comp hPcont).mul hdilcont).aestronglyMeasurable
  have hcomplex := integral_circleLebesgue_eq_circleAverage_complex
    (fun z => ((_root_.poissonKernel 0 w z : ℂ) * F ((r : ℂ) * z))) hmeas
  have hsmul : (fun z : ℂ => ((_root_.poissonKernel 0 w z : ℂ) * F ((r : ℂ) * z)))
      = (_root_.poissonKernel 0 w • fun z : ℂ => F ((r : ℂ) * z)) := by
    funext z
    simp [Complex.real_smul]
  rw [hsmul, circleAverage_poissonKernel_dilate hr0 hr1 hF hw] at hcomplex
  have hInt : Integrable
      (fun z : Circle => ((_root_.poissonKernel 0 w (z : ℂ) : ℂ) * F ((r : ℂ) * (z : ℂ))))
      circleLebesgue :=
    ((Complex.continuous_ofReal.comp hPcont).mul hdilcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcomm := Complex.reCLM.integral_comp_comm hInt
  rw [hcomplex] at hcomm
  simpa [Complex.mul_re] using hcomm

/-- **The Poisson integral against the boundary measure.** -/
theorem integral_poissonKernel_herglotzBoundaryMeasure {F : ℂ → ℂ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∫ ζ : Circle, _root_.poissonKernel 0 w (ζ : ℂ) ∂(herglotzBoundaryMeasure F r)
      = (F ((r : ℂ) * w)).re := by
  have hnn : ∀ ζ : Circle, 0 ≤ (F ((r : ℂ) * (ζ : ℂ))).re := by
    intro ζ
    refine hpos _ ?_
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, Circle.norm_coe, mul_one]
    exact hr1
  have hdens : Measurable (herglotzDensity F r) :=
    ENNReal.measurable_ofReal.comp
      ((Complex.continuous_re.comp (continuous_dilate_circle hr0 hr1 hF)).measurable)
  have hne : ∀ ζ : Circle, herglotzDensity F r ζ ≠ ⊤ := by
    intro ζ
    exact ENNReal.ofReal_ne_top
  rw [herglotzBoundaryMeasure,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall (fun ζ => (hne ζ).lt_top))]
  rw [← integral_poissonKernel_density hr0 hr1 hF hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  show (herglotzDensity F r ζ).toReal • _root_.poissonKernel 0 w (ζ : ℂ)
      = _root_.poissonKernel 0 w (ζ : ℂ) * ((F ((r : ℂ) * (ζ : ℂ))).re)
  unfold herglotzDensity
  rw [ENNReal.toReal_ofReal (hnn ζ), smul_eq_mul, mul_comm]

end

end GaloisForLFunctions.HTGeometry
