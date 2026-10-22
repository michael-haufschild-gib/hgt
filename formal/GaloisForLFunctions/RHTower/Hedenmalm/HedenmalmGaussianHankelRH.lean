import GaloisForLFunctions.RHTower.CompleteHankelSignCone
import GaloisForLFunctions.RHTower.GaussianWindowPolynomialDensity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedOrientationBoundary
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# A one-temperature complete Hankel criterion for RH

For each aperture `0 < a < 1/2`, take the actual Hedenmalm center-mixed Fourier current and form
all of its Gaussian-windowed moments at one arbitrary temperature `tau > 0`.  The complete tower
of finite Hankel sections is positive semidefinite if and only if that current is pointwise
nonnegative.  The existing exact Hedenmalm orientation theorem then identifies this condition with
the Riemann hypothesis.

The temperature is inessential: every single positive Gaussian temperature is complete, and the
truth of the complete Hankel condition is independent of the chosen temperature.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators ENNReal Real

namespace RHTower

/-- A positive Gaussian density charges every nonempty open subset of the real line. -/
instance gaussianWindowMeasure_isOpenPosMeasure (tau : ℝ) :
    (gaussianWindowMeasure tau).IsOpenPosMeasure where
  open_pos U hU hne := by
    intro hzero
    have hvolume : (volume : Measure ℝ) U ≠ 0 := hU.measure_ne_zero volume hne
    apply hvolume
    unfold gaussianWindowMeasure at hzero
    rw [withDensity_apply_eq_zero (by fun_prop)] at hzero
    have hset : {x : ℝ |
        ENNReal.ofReal (Real.exp (-tau * x ^ 2)) ≠ 0} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    rw [hset, Set.univ_inter] at hzero
    exact hzero

/-- The real Hedenmalm center-mixed Fourier current at aperture `a`. -/
def thetaCuspCenterMixedFourierCurrent
    (a : ℝ) (ha : |a| < 1) (b : ℝ) : ℝ :=
  (FourierTransform.fourier
    (thetaCuspHorizontalAutocorrelationTangent a ha)
    (b / (2 * Real.pi))).re

theorem continuous_thetaCuspCenterMixedFourierCurrent
    (a : ℝ) (ha : |a| < 1) :
    Continuous (thetaCuspCenterMixedFourierCurrent a ha) := by
  let f : SchwartzMap ℝ ℂ := thetaCuspHorizontalAutocorrelationTangent a ha
  have hfourier : Continuous (fun b : ℝ ↦
      (SchwartzMap.fourierTransformCLM ℂ f) (b / (2 * Real.pi))) :=
    (SchwartzMap.fourierTransformCLM ℂ f).continuous.comp
      (continuous_id.div_const (2 * Real.pi))
  have hre := Complex.continuous_re.comp hfourier
  simpa only [thetaCuspCenterMixedFourierCurrent, f,
    SchwartzMap.fourierTransformCLM_apply] using! hre

theorem thetaCuspCenterMixedFourierCurrent_memLp_top
    (tau a : ℝ) (ha : |a| < 1) :
    MemLp (thetaCuspCenterMixedFourierCurrent a ha) ∞
      (gaussianWindowMeasure tau) := by
  let f : SchwartzMap ℝ ℂ := thetaCuspHorizontalAutocorrelationTangent a ha
  refine memLp_top_of_bound
    (continuous_thetaCuspCenterMixedFourierCurrent a ha).aestronglyMeasurable
    ‖f.toLp 1‖ ?_
  filter_upwards with b
  have hre := abs_re_le_norm
    (FourierTransform.fourier f (b / (2 * Real.pi)))
  have hfourier := SchwartzMap.norm_fourier_apply_le_toLp_one
    f (b / (2 * Real.pi))
  simpa only [thetaCuspCenterMixedFourierCurrent, f, Real.norm_eq_abs] using
    hre.trans hfourier

/-- At a positive Gaussian temperature, the complete Hankel tower of the Hedenmalm current. -/
def HedenmalmGaussianHankelCone (tau : ℝ) : Prop :=
  ∀ (a : ℝ) (ha : |a| < 1), 0 < a → a < 1 / 2 →
    CompleteHankelCone
      (weightedMoment (gaussianWindowMeasure tau)
        (thetaCuspCenterMixedFourierCurrent a ha))

/-- For each aperture and positive temperature, the complete Gaussian Hankel tower is exactly the
pointwise sign condition on the Hedenmalm current. -/
theorem hedenmalmGaussianHankelCone_at_iff_pointwise
    {tau a : ℝ} (htau : 0 < tau) (ha : |a| < 1) :
    CompleteHankelCone
        (weightedMoment (gaussianWindowMeasure tau)
          (thetaCuspCenterMixedFourierCurrent a ha)) ↔
      ∀ b : ℝ, 0 ≤ thetaCuspCenterMixedFourierCurrent a ha b := by
  letI := gaussianWindowMeasure_finite htau
  exact completeHankelCone_weightedMoment_iff
    (gaussianWindowMeasure_hasEntireExponentialMoments htau)
    (thetaCuspCenterMixedFourierCurrent a ha)
    (continuous_thetaCuspCenterMixedFourierCurrent a ha)
    (thetaCuspCenterMixedFourierCurrent_memLp_top tau a ha)

/-- A fixed positive temperature complete Hankel condition is the actual Hedenmalm Fourier sign
condition. -/
theorem hedenmalmGaussianHankelCone_iff_fourierNonnegative
    {tau : ℝ} (htau : 0 < tau) :
    HedenmalmGaussianHankelCone tau ↔
      ThetaCuspCenterMixedFourierNonnegative := by
  constructor
  · intro h a ha ha0 hahalf b
    have hb := (hedenmalmGaussianHankelCone_at_iff_pointwise htau ha).mp
      (h a ha ha0 hahalf) b
    exact hb
  · intro h a ha ha0 hahalf
    apply (hedenmalmGaussianHankelCone_at_iff_pointwise htau ha).mpr
    intro b
    exact h a ha ha0 hahalf b

/-- **One-temperature complete Hankel criterion for RH.** At every arbitrarily chosen positive
Gaussian temperature, positivity of all finite Hedenmalm moment sections is equivalent to the
Riemann hypothesis. -/
theorem hedenmalmGaussianHankelCone_iff_riemannHypothesis
    {tau : ℝ} (htau : 0 < tau) :
    HedenmalmGaussianHankelCone tau ↔ RiemannHypothesis :=
  (hedenmalmGaussianHankelCone_iff_fourierNonnegative htau).trans
    thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis

/-- **Temperature invariance.** Complete Hedenmalm Hankel positivity cannot depend on which
positive Gaussian temperature is used. -/
theorem hedenmalmGaussianHankelCone_temperature_iff
    {tau sigma : ℝ} (htau : 0 < tau) (hsigma : 0 < sigma) :
    HedenmalmGaussianHankelCone tau ↔ HedenmalmGaussianHankelCone sigma :=
  (hedenmalmGaussianHankelCone_iff_riemannHypothesis htau).trans
    (hedenmalmGaussianHankelCone_iff_riemannHypothesis hsigma).symm

/-- Existence of one successful positive temperature is already equivalent to RH. -/
theorem exists_hedenmalmGaussianHankelCone_iff_riemannHypothesis :
    (∃ tau : ℝ, 0 < tau ∧ HedenmalmGaussianHankelCone tau) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨tau, htau, hcone⟩
    exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis htau).mp hcone
  · intro hRH
    refine ⟨1, by norm_num, ?_⟩
    exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis (by norm_num)).mpr hRH

/-- Simultaneous positivity at every positive temperature is equivalent to RH. -/
theorem forall_hedenmalmGaussianHankelCone_iff_riemannHypothesis :
    (∀ tau : ℝ, 0 < tau → HedenmalmGaussianHankelCone tau) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis (by norm_num : (0 : ℝ) < 1)).mp
      (h 1 (by norm_num))
  · intro hRH tau htau
    exact (hedenmalmGaussianHankelCone_iff_riemannHypothesis htau).mpr hRH

end RHTower
