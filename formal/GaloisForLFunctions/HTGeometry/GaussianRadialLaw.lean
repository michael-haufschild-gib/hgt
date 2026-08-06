import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The standard Gaussian measure as a density against Lebesgue measure

`ProbabilityTheory.stdGaussian E` is defined through its coordinates in an
orthonormal basis.  This file identifies it, on a Euclidean space, with the
Lebesgue measure weighted by the classical Gaussian density
`(2 π)^{-m/2} exp(-‖x‖²/2)`.

The identification proceeds through the coordinate product measure: the finite
product of one-dimensional Gaussians is the product Lebesgue measure weighted by
the product of the one-dimensional Gaussian densities, and the coordinate map of
a Euclidean space preserves volume.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The coordinate Gaussian density of a finite product of standard real
Gaussians. -/
def coordinateGaussianDensityReal (x : ι → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem coordinateGaussianDensityReal_nonneg (x : ι → ℝ) :
    0 ≤ coordinateGaussianDensityReal x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

theorem measurable_coordinateGaussianDensityReal :
    Measurable (coordinateGaussianDensityReal (ι := ι)) := by
  unfold coordinateGaussianDensityReal
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

/-- **Product Gaussian density.**  The finite product of standard real Gaussians
is the product Lebesgue measure weighted by the product of the one-dimensional
Gaussian densities. -/
theorem measure_pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (coordinateGaussianDensityReal x)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hintegrable : ∀ i : ι,
      Integrable (gaussianPDFReal 0 1) ((volume : Measure ℝ).restrict (s i)) :=
    fun i => (integrable_gaussianPDFReal 0 1).restrict
  have hprodInt : Integrable (coordinateGaussianDensityReal (ι := ι))
      (Measure.pi fun i => (volume : Measure ℝ).restrict (s i)) :=
    Integrable.fintype_prod hintegrable
  have hnonneg : (0 : (ι → ℝ) → ℝ)
      ≤ᵐ[Measure.pi fun i => (volume : Measure ℝ).restrict (s i)]
      coordinateGaussianDensityReal := by
    filter_upwards with x
    simpa using coordinateGaussianDensityReal_nonneg x
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    ← ofReal_integral_eq_lintegral_ofReal hprodInt hnonneg]
  rw [show (∫ x, coordinateGaussianDensityReal x
        ∂(Measure.pi fun i => (volume : Measure ℝ).restrict (s i)))
      = ∏ i, ∫ y in s i, gaussianPDFReal 0 1 y from
    integral_fintype_prod_eq_prod (fun _ : ι => gaussianPDFReal 0 1)]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y => gaussianPDFReal_nonneg 0 1 y)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs i),
    gaussianPDF_def, ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_gaussianPDFReal 0 1).restrict)
      (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]

/-- Pushing a density through a measurable equivalence. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext t ht
  rw [withDensity_apply _ ht, Measure.restrict_map e.measurable ht]
  rw [show (∫⁻ y : β, f (e.symm y) ∂(Measure.map (⇑e) (μ.restrict (⇑e ⁻¹' t))))
      = ∫⁻ x : α, f (e.symm (e x)) ∂(μ.restrict (⇑e ⁻¹' t)) from
    lintegral_map (hf.comp e.symm.measurable) e.measurable]
  simp only [MeasurableEquiv.symm_apply_apply]
  rw [Measure.map_apply e.measurable ht, withDensity_apply _ (e.measurable ht)]

/-- The classical Gaussian density on a Euclidean space. -/
def euclideanGaussianDensityReal (x : EuclideanSpace ℝ ι) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ (Fintype.card ι) * Real.exp (-‖x‖ ^ 2 / 2)

theorem euclideanGaussianDensityReal_nonneg (x : EuclideanSpace ℝ ι) :
    0 ≤ euclideanGaussianDensityReal x := by
  unfold euclideanGaussianDensityReal
  positivity

theorem coordinateGaussianDensityReal_ofLp (x : EuclideanSpace ℝ ι) :
    coordinateGaussianDensityReal x.ofLp = euclideanGaussianDensityReal x := by
  have hsq : ‖x‖ ^ 2 = ∑ i, (x.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt
      (Finset.sum_nonneg fun i _ => by positivity)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Real.norm_eq_abs, sq_abs]
  unfold coordinateGaussianDensityReal euclideanGaussianDensityReal
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show gaussianPDFReal 0 1 (x.ofLp i)
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x.ofLp i) ^ 2 / 2) by
      unfold gaussianPDFReal
      norm_num)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.exp_sum, hsq, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- **The standard Gaussian is the Lebesgue measure weighted by the classical
Gaussian density.** -/
theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ ι)
      = (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (euclideanGaussianDensityReal x)) := by
  have hmeas : Measurable
      (fun x : ι → ℝ => ENNReal.ofReal (coordinateGaussianDensityReal x)) :=
    ENNReal.measurable_ofReal.comp measurable_coordinateGaussianDensityReal
  have hvol : (volume : Measure (ι → ℝ)).map (MeasurableEquiv.toLp 2 (ι → ℝ))
      = (volume : Measure (EuclideanSpace ℝ ι)) :=
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm).map_eq
  rw [← map_pi_eq_stdGaussian, ← MeasurableEquiv.coe_toLp,
    measure_pi_gaussianReal_eq_withDensity,
    map_withDensity_measurableEquiv _ (MeasurableEquiv.toLp 2 (ι → ℝ)) hmeas, hvol]
  congr 1
  funext x
  congr 1
  exact coordinateGaussianDensityReal_ofLp x

end

end GaloisForLFunctions.HTGeometry
