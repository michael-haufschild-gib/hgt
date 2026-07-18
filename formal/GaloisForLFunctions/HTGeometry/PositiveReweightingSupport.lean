import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform
import Mathlib.MeasureTheory.Measure.Support

/-!
# Positive reweighting preserves the support

The genericity argument is applied not to the base Herglotz measure but to its reweightings.  Since
the control map is only linear in the *density*, the tangent direction at a base reweighting is the
Cauchy-jet map of the reweighted measure, and surjectivity there needs that measure to still have
infinite support.

A density that is almost everywhere nonzero does not move the null sets, and the support is defined
by positivity of the measure on neighbourhoods, so the support is unchanged.  In particular the
Nevanlinna-weighted measure of a base measure with infinite support again has infinite support: its
density is a product of a strictly positive weight and an exponential.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

/-- An almost everywhere nonzero density does not change the null sets. -/
theorem measure_withDensity_eq_zero_iff (μ : Measure ℝ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hpos : ∀ᵐ t ∂μ, g t ≠ 0) (s : Set ℝ) :
    μ.withDensity g s = 0 ↔ μ s = 0 := by
  rw [withDensity_apply_eq_zero hg]
  constructor
  · intro h
    have hnull : μ ({x | g x = 0} ∩ s) = 0 := by
      apply measure_mono_null Set.inter_subset_left
      rw [MeasureTheory.ae_iff] at hpos
      simpa using hpos
    have hcover : s ⊆ ({x | g x ≠ 0} ∩ s) ∪ ({x | g x = 0} ∩ s) := by
      intro y hy
      by_cases hgy : g y = 0
      · exact Or.inr ⟨hgy, hy⟩
      · exact Or.inl ⟨hgy, hy⟩
    exact measure_mono_null hcover (measure_union_null h hnull)
  · intro h
    exact measure_mono_null Set.inter_subset_right h

/-- **Positive reweighting preserves the support.** -/
theorem support_withDensity_eq (μ : Measure ℝ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hpos : ∀ᵐ t ∂μ, g t ≠ 0) :
    (μ.withDensity g).support = μ.support := by
  have hiff : ∀ u : Set ℝ, (0 < μ.withDensity g u) ↔ (0 < μ u) := by
    intro u
    rw [pos_iff_ne_zero, pos_iff_ne_zero, ne_eq, ne_eq,
      measure_withDensity_eq_zero_iff μ hg hpos u]
  ext x
  simp only [Measure.support, Set.mem_setOf_eq]
  exact Filter.frequently_congr (Filter.Eventually.of_forall hiff)

/-- The Nevanlinna weight times an exponential is a strictly positive density. -/
theorem nevanlinnaWeightedDensity_ne_zero (u : ℝ → ℝ) (t : ℝ) :
    (Real.toNNReal (nevanlinnaWeight t * Real.exp (u t)) : ℝ≥0∞) ≠ 0 := by
  have hpos : 0 < nevanlinnaWeight t * Real.exp (u t) :=
    mul_pos (nevanlinnaWeight_pos t) (Real.exp_pos _)
  simp only [ne_eq, ENNReal.coe_eq_zero]
  rw [← NNReal.coe_eq_zero, Real.coe_toNNReal _ (le_of_lt hpos)]
  exact ne_of_gt hpos

/-- **The Nevanlinna-weighted measure keeps the support.**  Reweighting by the Nevanlinna weight
and an exponential is a strictly positive density, so it moves no null set. -/
theorem support_nevanlinnaWeightedMeasure (μ : Measure ℝ) (u : ℝ → ℝ)
    (hu : Measurable u) :
    (nevanlinnaWeightedMeasure μ u).support = μ.support := by
  rw [nevanlinnaWeightedMeasure]
  apply support_withDensity_eq
  · apply Measurable.coe_nnreal_ennreal
    apply Measurable.real_toNNReal
    apply Measurable.mul
    · unfold nevanlinnaWeight
      fun_prop
    · exact Real.measurable_exp.comp hu
  · filter_upwards with t
    exact nevanlinnaWeightedDensity_ne_zero u t

/-- Infinite support passes to the Nevanlinna-weighted measure, so the genericity theorems apply at
every base reweighting. -/
theorem support_nevanlinnaWeightedMeasure_infinite (μ : Measure ℝ) (u : ℝ → ℝ)
    (hu : Measurable u) (hsupp : μ.support.Infinite) :
    (nevanlinnaWeightedMeasure μ u).support.Infinite := by
  rw [support_nevanlinnaWeightedMeasure μ u hu]
  exact hsupp

end

end GaloisForLFunctions.HTGeometry
