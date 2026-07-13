import Mathlib

/-!
# Total variation of a mutually-singular difference

For finite measures `μ ⟂ ν`, the signed measure `μ − ν` has Jordan decomposition `(μ, ν)`, so its
total variation is `μ + ν`.  In particular `‖μ − ν‖_TV = μ(univ) + ν(univ)`.  This is the isometric
core of the `N`-extremal simplex step (`indeterminate-moment-fiber-maximal-translation-ht`, eq. (22)):
distinct `N`-extremal representing measures are mutually singular, so real combinations sit
isometrically in total-variation geometry.
-/

open MeasureTheory

namespace HTGeometry

/-- The Jordan decomposition of a mutually-singular difference is the pair itself. -/
theorem toJordanDecomposition_toSignedMeasure_sub {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition = ⟨μ, ν, h⟩ :=
  SignedMeasure.toJordanDecomposition_eq (by rw [JordanDecomposition.toSignedMeasure])

/-- **Total variation of a mutually-singular difference.** For finite `μ ⟂ ν`, the total variation
of `μ − ν` is `μ + ν`. -/
theorem totalVariation_toSignedMeasure_sub {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation = μ + ν := by
  rw [SignedMeasure.totalVariation, toJordanDecomposition_toSignedMeasure_sub μ ν h]

/-- Total-variation mass of a mutually-singular difference of probabilities is `2`. -/
theorem totalVariation_univ_eq_of_isProbability {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ ⟂ₘ ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ = 2 := by
  rw [totalVariation_toSignedMeasure_sub μ ν h, Measure.add_apply,
    measure_univ, measure_univ, one_add_one_eq_two]

end HTGeometry
