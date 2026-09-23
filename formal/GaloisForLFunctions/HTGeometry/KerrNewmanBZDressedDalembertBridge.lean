import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovSmoothMetricBridge

/-!
# Wave operator of the flat Belinski--Zakharov-dressed Kerr--Newman metric

The constant full-coordinate BZ lift already has an explicit inverse and determinant `-1`.
Using the existing smooth-metric-chart d'Alembertian, this file proves its exact wave operator.
The unipotent dressing produces the two `t--φ` mixed second derivatives, while the density remains
one.

This is a flat coordinate-chart calculation for the constant BZ lift.  It neither calculates the
wave operator of the curved Kerr--Newman metric nor proves an Einstein--Maxwell solution.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

/-- The d'Alembertian of the full flat BZ lift has constant coefficients given by its explicit
inverse metric. -/
theorem kerrNewmanFlatBZDressedSmoothMetric_dalembert
    (parameter : ℝ) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin 4 → ℝ) :
    (kerrNewmanFlatBZDressedSmoothMetric parameter).chart.dalembert f x =
      ∑ i, ∑ j, kerrNewmanFlatBZDressedMetricInverse parameter i j *
        coordPartial i (coordPartial j f) x := by
  have hinv : ∀ y : Fin 4 → ℝ,
      (kerrNewmanFlatBZDressedSmoothMetric parameter).chart.inverseMetric y =
        kerrNewmanFlatBZDressedMetricInverse parameter := by
    intro y
    rw [SmoothPseudoMetric.chart_inverseMetric,
      kerrNewmanFlatBZDressedSmoothMetric_metric]
    exact Matrix.inv_eq_right_inv (kerrNewmanFlatBZDressedMetric_mul_inverse parameter)
  have hdensity : ∀ y : Fin 4 → ℝ,
      (kerrNewmanFlatBZDressedSmoothMetric parameter).chart.density y = 1 := by
    intro y
    rw [SmoothPseudoMetric.chart_density,
      kerrNewmanFlatBZDressedSmoothMetric_metric,
      kerrNewmanFlatBZDressedMetric_det]
    norm_num
  have hflux : ∀ i : Fin 4,
      (kerrNewmanFlatBZDressedSmoothMetric parameter).chart.flux f i =
        fun y => ∑ j, kerrNewmanFlatBZDressedMetricInverse parameter i j *
          coordPartial j f y := by
    intro i
    funext y
    simp only [SmoothMetricChart.flux]
    rw [hdensity y, hinv y]
    simp
  have hderiv : ∀ i : Fin 4,
      coordPartial i ((kerrNewmanFlatBZDressedSmoothMetric parameter).chart.flux f i) x =
        ∑ j, kerrNewmanFlatBZDressedMetricInverse parameter i j *
          coordPartial i (coordPartial j f) x := by
    intro i
    rw [hflux i]
    rw [coordPartial_sum (fun j _ =>
      (differentiableAt_of_contDiff_infty (contDiff_coordPartial hf j) x).const_mul
        (kerrNewmanFlatBZDressedMetricInverse parameter i j)) i]
    apply Finset.sum_congr rfl
    intro j _
    rw [coordPartial_const_mul
      (differentiableAt_of_contDiff_infty (contDiff_coordPartial hf j) x)
      (kerrNewmanFlatBZDressedMetricInverse parameter i j) i]
  simp only [SmoothMetricChart.dalembert, hdensity, inv_one]
  rw [Finset.sum_congr rfl fun i _ => hderiv i]
  simp

/-- Expanded four-coordinate wave operator.  The two mixed terms are the exact imprint of the
unipotent BZ `t--φ` shear. -/
theorem kerrNewmanFlatBZDressedSmoothMetric_dalembert_explicit
    (parameter : ℝ) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin 4 → ℝ) :
    (kerrNewmanFlatBZDressedSmoothMetric parameter).chart.dalembert f x =
      -coordPartial 0 (coordPartial 0 f) x +
        parameter * coordPartial 0 (coordPartial 3 f) x +
          coordPartial 1 (coordPartial 1 f) x +
            coordPartial 2 (coordPartial 2 f) x +
              parameter * coordPartial 3 (coordPartial 0 f) x +
                (1 - parameter ^ (2 : ℕ)) * coordPartial 3 (coordPartial 3 f) x := by
  rw [kerrNewmanFlatBZDressedSmoothMetric_dalembert parameter hf x]
  simp [kerrNewmanFlatBZDressedMetricInverse, Fin.sum_univ_four]
  ring

end GaloisForLFunctions.HTGeometry
