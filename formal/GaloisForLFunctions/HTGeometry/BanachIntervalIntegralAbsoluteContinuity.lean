import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute continuity of Banach-valued interval primitives

Mathlib's interval-primitive absolute-continuity theorem is currently stated for real-valued
integrands.  The proof is norm-valued and extends verbatim to every real normed vector space.
This module supplies that extension, which is needed for complex-valued weak ODEs.
-/

open MeasureTheory Set Filter Function
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Banach-valued interval integral, as a function of its upper endpoint, is absolutely
continuous on every interval where its integrand is interval integrable. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
    {f : ℝ → E} {a b c : ℝ} (h : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have htend : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have htend' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp htend
  refine squeeze_zero' ?_ ?_ htend'
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [Function.comp_apply, s]
  have hdisj : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hdisj] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := Set.mem_setOf_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
          (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm, norm_neg,
      intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
      (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set h.def'.norm hsubset |>.integrable

/-- Composition with a Lipschitz map preserves absolute continuity on a real interval. -/
theorem LipschitzWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : NNReal} {g : X → Y} {f : ℝ → X} {a b : ℝ}
    (hg : LipschitzWith K g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ g (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  have hlim : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) ↦
        (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hf)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with E
    exact Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  · filter_upwards with E
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ hg.dist_le_mul _ _

/-- Applying a continuous linear map to an absolutely continuous Banach-valued path preserves
absolute continuity. -/
theorem ContinuousLinearMap.comp_absolutelyContinuousOnInterval
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ L (f x)) a b :=
  GaloisForLFunctions.HTGeometry.LipschitzWith.comp_absolutelyContinuousOnInterval
    L.lipschitz hf

end GaloisForLFunctions.HTGeometry
