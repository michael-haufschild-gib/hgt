import GaloisForLFunctions.HTGeometry.EvenWeightedSignCarrier

/-!
# Reflection on an even positive weighted Hilbert space

For an even positive weight on the real line, pullback by `x ↦ -x` preserves the weighted
measure.  This module constructs the resulting unitary involution on weighted `L²` and records its
literal almost-everywhere action.  The construction is independent of any spectral route.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {w : ℝ → ℝ}

/-- Reflection preserves a measure with even real density. -/
theorem map_neg_positiveWeightedMeasure (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) :
    Measure.map (fun x : ℝ => -x)
        ((volume : Measure ℝ).withDensity (realDensity w)) =
      (volume : Measure ℝ).withDensity (realDensity w) := by
  rw [map_withDensity_of_involution measurable_neg (fun x => neg_neg x)
    (Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq
    (measurable_realDensity hw)]
  congr 1
  funext x
  simp [realDensity, heven]

theorem measurePreserving_neg_positiveWeightedMeasure (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) :
    MeasurePreserving (fun x : ℝ => -x)
      ((volume : Measure ℝ).withDensity (realDensity w))
      ((volume : Measure ℝ).withDensity (realDensity w)) :=
  ⟨measurable_neg, map_neg_positiveWeightedMeasure hw heven⟩

/-- Pullback by reflection on an even positive weighted `L²` space. -/
def positiveWeightedReflection (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) :
    WeightedL2 (μ := volume) w →L[ℂ] WeightedL2 (μ := volume) w :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    (measurePreserving_neg_positiveWeightedMeasure hw heven)).toContinuousLinearMap

/-- The weighted reflection is literal source reflection almost everywhere. -/
theorem positiveWeightedReflection_ae (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (heven : ∀ x, w (-x) = w x) (f : WeightedL2 (μ := volume) w) :
    positiveWeightedReflection hw heven f =ᵐ[(volume : Measure ℝ)] fun x => f (-x) := by
  apply (withDensity_realDensity_ae_eq hw hpos).mp
  exact Lp.coeFn_compMeasurePreserving f
    (measurePreserving_neg_positiveWeightedMeasure hw heven)

@[simp] theorem positiveWeightedReflection_involutive (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) (f : WeightedL2 (μ := volume) w) :
    positiveWeightedReflection hw heven (positiveWeightedReflection hw heven f) = f := by
  apply Lp.ext
  have hinner := (Lp.coeFn_compMeasurePreserving f
    (measurePreserving_neg_positiveWeightedMeasure hw heven)).comp_tendsto
      (measurePreserving_neg_positiveWeightedMeasure hw heven).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (positiveWeightedReflection hw heven f)
      (measurePreserving_neg_positiveWeightedMeasure hw heven), hinner] with x hout hin
  change ((Lp.compMeasurePreserving (fun x : ℝ => -x)
      (measurePreserving_neg_positiveWeightedMeasure hw heven)
      (positiveWeightedReflection hw heven f) : WeightedL2 (μ := volume) w) : ℝ → ℂ) x = f x
  rw [hout]
  change ((Lp.compMeasurePreserving (fun x : ℝ => -x)
      (measurePreserving_neg_positiveWeightedMeasure hw heven) f :
        WeightedL2 (μ := volume) w) : ℝ → ℂ) (-x) = f x
  simpa only [Function.comp_apply, neg_neg] using hin

theorem norm_positiveWeightedReflection (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) (f : WeightedL2 (μ := volume) w) :
    ‖positiveWeightedReflection hw heven f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    (measurePreserving_neg_positiveWeightedMeasure hw heven)).norm_map f

/-- Reflection as an onto linear isometry, with itself as inverse. -/
def positiveWeightedReflectionLIE (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) :
    WeightedL2 (μ := volume) w ≃ₗᵢ[ℂ] WeightedL2 (μ := volume) w where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
    (measurePreserving_neg_positiveWeightedMeasure hw heven)
  invFun := positiveWeightedReflection hw heven
  left_inv := positiveWeightedReflection_involutive hw heven
  right_inv := positiveWeightedReflection_involutive hw heven

@[simp] theorem positiveWeightedReflectionLIE_apply (hw : Measurable w)
    (heven : ∀ x, w (-x) = w x) (f : WeightedL2 (μ := volume) w) :
    positiveWeightedReflectionLIE hw heven f = positiveWeightedReflection hw heven f := rfl

end

end GaloisForLFunctions.HTGeometry
