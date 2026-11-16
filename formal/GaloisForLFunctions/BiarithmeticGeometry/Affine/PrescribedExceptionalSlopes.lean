import GaloisForLFunctions.BiarithmeticGeometry.Affine.CountableExceptionalDirections
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Prescribing exceptional directions with diffuse Gaussian line spectra

A geometric mixture of Gaussian measures on lines has exactly the prescribed
sequence of exceptional slopes. Thus countability is the sharp directional
restriction: even dense countable sets occur for diffuse probability spectra.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.BiarithmeticGeometry

local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal one_ne_zero

private theorem spectralLine_measurable (p : ℝ × ℝ) : MeasurableSet (affineSpectralLine p) :=
  (isClosed_eq continuous_snd
    ((continuous_const.mul continuous_fst).add continuous_const)).measurableSet

/-- Standard Gaussian measure carried by the line of slope `a` through the origin. -/
def gaussianSlopeMeasure (a : ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).map (fun t : ℝ => (t, a * t))

private theorem gaussianSlopeMap_measurable (a : ℝ) :
    Measurable (fun t : ℝ => (t, a * t)) := by fun_prop

instance gaussianSlopeMeasure_probability (a : ℝ) : IsProbabilityMeasure (gaussianSlopeMeasure a) :=
  Measure.isProbabilityMeasure_map (gaussianSlopeMap_measurable a).aemeasurable

instance gaussianSlopeMeasure_noAtoms (a : ℝ) : NullSingletonClass (gaussianSlopeMeasure a) where
  measure_singleton x := by
    rw [gaussianSlopeMeasure, Measure.map_apply (gaussianSlopeMap_measurable a)
      (measurableSet_singleton x)]
    apply measure_mono_null _ (measure_singleton (μ := gaussianReal 0 1) x.1)
    intro t ht
    change (t, a * t) = x at ht
    exact congrArg Prod.fst ht

/-- An affine line carries full mass only when both slope and intercept agree. -/
theorem gaussianSlopeMeasure_line (a : ℝ) (p : ℝ × ℝ) :
    gaussianSlopeMeasure a (affineSpectralLine p) = if p = (a, 0) then 1 else 0 := by
  classical
  rw [gaussianSlopeMeasure, Measure.map_apply (gaussianSlopeMap_measurable a)
    (spectralLine_measurable p)]
  split_ifs with hp
  · subst p
    have he : (fun t : ℝ => (t, a * t)) ⁻¹' affineSpectralLine (a, 0) = univ := by
      ext t
      simp [affineSpectralLine]
    rw [he, measure_univ]
  · by_cases ha : a = p.1
    · have hp2 : p.2 ≠ 0 := by
        intro h
        exact hp (Prod.ext ha.symm h)
      have he : (fun t : ℝ => (t, a * t)) ⁻¹' affineSpectralLine p = ∅ := by
        ext t
        simp only [mem_preimage, affineSpectralLine, mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro h
        exact hp2 (by rw [ha] at h; linarith only [h])
      rw [he, measure_empty]
    · apply measure_mono_null _ (measure_singleton (μ := gaussianReal 0 1) (p.2 / (a - p.1)))
      intro t ht
      change a * t = p.1 * t + p.2 at ht
      apply (eq_div_iff (sub_ne_zero.mpr ha)).mpr
      linear_combination ht

/-- A probability mixture realizing the listed exceptional slopes, including repetitions. -/
def prescribedSlopeMeasure (a : ℕ → ℝ) : Measure (ℝ × ℝ) :=
  Measure.sum (fun n => ((2⁻¹ : ℝ≥0∞) ^ (n + 1)) • gaussianSlopeMeasure (a n))

instance prescribedSlopeMeasure_probability (a : ℕ → ℝ) :
    IsProbabilityMeasure (prescribedSlopeMeasure a) where
  measure_univ := by
    simp only [prescribedSlopeMeasure, Measure.sum_apply _ MeasurableSet.univ,
      Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance prescribedSlopeMeasure_noAtoms (a : ℕ → ℝ) :
    NullSingletonClass (prescribedSlopeMeasure a) where
  measure_singleton x := by
    simp only [prescribedSlopeMeasure, Measure.sum_apply _ (measurableSet_singleton x), Measure.smul_apply,
      measure_singleton, smul_eq_mul, mul_zero, tsum_zero]

/-- Every listed slope, and no other slope, obstructs directional mean-square decay. -/
theorem exceptionalSpectralSlopes_prescribed (a : ℕ → ℝ) :
    exceptionalSpectralSlopes (prescribedSlopeMeasure a) = range a := by
  classical
  ext s
  constructor
  · rintro ⟨b, hb⟩
    by_contra h
    have hne : ∀ n, (s, b) ≠ (a n, 0) := by
      intro n hn
      exact h ⟨n, (congrArg Prod.fst hn).symm⟩
    simp only [prescribedSlopeMeasure, Measure.sum_apply _ (spectralLine_measurable (s, b)),
      Measure.smul_apply,
      gaussianSlopeMeasure_line, if_neg (hne _), smul_eq_mul, mul_zero, tsum_zero] at hb
    exact lt_irrefl _ hb
  · rintro ⟨n, rfl⟩
    refine ⟨0, ?_⟩
    have hle := Measure.le_sum (fun k => ((2⁻¹ : ℝ≥0∞) ^ (k + 1)) •
      gaussianSlopeMeasure (a k)) n (affineSpectralLine (a n, 0))
    have hn : 0 < (2⁻¹ : ℝ≥0∞) ^ (n + 1) := ENNReal.pow_pos (by norm_num) _
    apply lt_of_lt_of_le hn
    simpa only [Measure.smul_apply, gaussianSlopeMeasure_line, if_true,
      smul_eq_mul, mul_one, prescribedSlopeMeasure] using hle


/-- A vertical Gaussian has no exceptional finite slope. -/
def verticalGaussianMeasure : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).map (fun t : ℝ => (0, t))

private theorem verticalGaussianMap_measurable :
    Measurable (fun t : ℝ => ((0 : ℝ), t)) := by fun_prop

instance verticalGaussianMeasure_probability : IsProbabilityMeasure verticalGaussianMeasure :=
  Measure.isProbabilityMeasure_map verticalGaussianMap_measurable.aemeasurable

instance verticalGaussianMeasure_noAtoms : NullSingletonClass verticalGaussianMeasure where
  measure_singleton x := by
    rw [verticalGaussianMeasure, Measure.map_apply verticalGaussianMap_measurable
      (measurableSet_singleton x)]
    apply measure_mono_null _ (measure_singleton (μ := gaussianReal 0 1) x.2)
    intro t ht
    change (0, t) = x at ht
    exact congrArg Prod.snd ht

theorem exceptionalSpectralSlopes_verticalGaussian :
    exceptionalSpectralSlopes verticalGaussianMeasure = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro a ⟨b, hb⟩
  have he : verticalGaussianMeasure (affineSpectralLine (a, b)) = 0 := by
    rw [verticalGaussianMeasure, Measure.map_apply verticalGaussianMap_measurable
      (spectralLine_measurable (a, b))]
    have hs : (fun t : ℝ => ((0 : ℝ), t)) ⁻¹' affineSpectralLine (a, b) = {b} := by
      ext t
      simp only [mem_preimage, affineSpectralLine, mem_setOf_eq, mul_zero, zero_add,
        mem_singleton_iff]
    rw [hs, measure_singleton]
  rw [he] at hb
  exact lt_irrefl _ hb

/-- Countability is the complete restriction on exceptional finite slopes of diffuse
probability spectra. The empty set and dense countable sets are both realized. -/
theorem countable_iff_diffuse_probability_exceptionalSlopes (S : Set ℝ) :
    S.Countable ↔ ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
      NullSingletonClass μ ∧ exceptionalSpectralSlopes μ = S := by
  constructor
  · intro hc
    by_cases hs : S.Nonempty
    · obtain ⟨a, ha⟩ := hc.exists_eq_range hs
      refine ⟨prescribedSlopeMeasure a, inferInstance, inferInstance, ?_⟩
      exact (exceptionalSpectralSlopes_prescribed a).trans ha.symm
    · refine ⟨verticalGaussianMeasure, inferInstance, inferInstance, ?_⟩
      rw [exceptionalSpectralSlopes_verticalGaussian, not_nonempty_iff_eq_empty.mp hs]
  · rintro ⟨μ, hp, hn, rfl⟩
    letI := hp
    exact (exceptionalSpectralSlopes_countable_iff μ).mpr hn

end GaloisForLFunctions.BiarithmeticGeometry


