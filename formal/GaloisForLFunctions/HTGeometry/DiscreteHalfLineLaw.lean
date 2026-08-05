import GaloisForLFunctions.HTGeometry.QuantileCoupling

/-!
# Discrete laws on the half line

A countable family of points carrying nonnegative weights defines a law on the line.  This file
records its total mass, its measure of a set, its integrals, and the criterion making it a law on
the half line.  The arithmetic clocks of a Dirichlet weight are of this shape: the points are the
logarithms of the integers and the weights are the normalized Dirichlet coefficients, so the
Laplace transform of such a law is the Dirichlet series at a shifted abscissa.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The law of a countable family of points carrying nonnegative weights. -/
def weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) : Measure ℝ :=
  Measure.sum fun i => w i • Measure.dirac (x i)

theorem weightedPointLaw_apply (x : ι → ℝ) (w : ι → ℝ≥0∞) {s : Set ℝ} (hs : MeasurableSet s) :
    weightedPointLaw x w s = ∑' i, s.indicator (fun _ => w i) (x i) := by
  rw [weightedPointLaw, Measure.sum_apply _ hs]
  refine tsum_congr fun i => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  by_cases hx : x i ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

@[simp] theorem weightedPointLaw_univ (x : ι → ℝ) (w : ι → ℝ≥0∞) :
    weightedPointLaw x w univ = ∑' i, w i := by
  rw [weightedPointLaw_apply x w MeasurableSet.univ]
  simp

/-- A weight family of total mass one gives a law. -/
theorem isProbabilityMeasure_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞)
    (hw : ∑' i, w i = 1) : IsProbabilityMeasure (weightedPointLaw x w) :=
  ⟨by rw [weightedPointLaw_univ]; exact hw⟩

/-- Lower integrals against a discrete law are weighted sums. -/
theorem lintegral_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(weightedPointLaw x w) = ∑' i, w i * f (x i) := by
  rw [weightedPointLaw, lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

/-- Integrals against a discrete law are weighted sums. -/
theorem integral_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) {f : ℝ → ℝ}
    (hf : Integrable f (weightedPointLaw x w)) :
    ∫ y, f y ∂(weightedPointLaw x w) = ∑' i, (w i).toReal * f (x i) := by
  rw [weightedPointLaw] at hf ⊢
  rw [integral_sum_measure hf]
  refine tsum_congr fun i => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]

/-- A discrete law carried by nonnegative points charges no negative half line. -/
theorem weightedPointLaw_Iio_zero (x : ι → ℝ) (w : ι → ℝ≥0∞) (hx : ∀ i, 0 ≤ x i) :
    weightedPointLaw x w (Iio 0) = 0 := by
  rw [weightedPointLaw_apply x w measurableSet_Iio]
  have hzero : ∀ i, (Iio (0 : ℝ)).indicator (fun _ => w i) (x i) = 0 := fun i =>
    Set.indicator_of_notMem (by simpa using hx i) _
  simp [hzero]

/-- The survival function of a discrete law. -/
theorem survival_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) (t : ℝ) :
    survival (weightedPointLaw x w) t
      = (∑' i, (Ioi t).indicator (fun _ => w i) (x i)).toReal := by
  rw [survival, Measure.real, weightedPointLaw_apply x w measurableSet_Ioi]

/-- **Laplace transform of a discrete law.**  It is the weighted sum of the exponentials of the
points, so for logarithmic points it is a Dirichlet series at a shifted abscissa. -/
theorem lintegral_exp_neg_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) (u : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-(u * y))) ∂(weightedPointLaw x w)
      = ∑' i, w i * ENNReal.ofReal (Real.exp (-(u * x i))) := by
  refine lintegral_weightedPointLaw x w ?_
  exact (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).ennreal_ofReal

/-- Real Laplace transform of a discrete law. -/
theorem integral_exp_neg_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞) (u : ℝ)
    (hint : Integrable (fun y => Real.exp (-(u * y))) (weightedPointLaw x w)) :
    ∫ y, Real.exp (-(u * y)) ∂(weightedPointLaw x w)
      = ∑' i, (w i).toReal * Real.exp (-(u * x i)) :=
  integral_weightedPointLaw x w hint

/-- **Mean of a discrete law.** -/
theorem integral_id_weightedPointLaw (x : ι → ℝ) (w : ι → ℝ≥0∞)
    (hint : Integrable (id : ℝ → ℝ) (weightedPointLaw x w)) :
    ∫ y, y ∂(weightedPointLaw x w) = ∑' i, (w i).toReal * x i :=
  integral_weightedPointLaw x w hint

end

end GaloisForLFunctions.HTGeometry
