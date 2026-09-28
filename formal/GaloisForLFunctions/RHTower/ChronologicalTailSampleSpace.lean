import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The sampling Hilbert space `L²([1, 2])`

The fixed-tail obstruction is run in the complex Hilbert space `L²([1, 2], du)`.  This module
provides a total embedding `toSample` of functions into it (zero outside `L²`), its inner-product
and norm formulas, linearity, and the fact that a.e. equality of functions continuous on `[1, 2]`
is equality on `[1, 2]`.
-/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace RHTower

/-- Lebesgue measure on the sampling interval `[1, 2]`. -/
abbrev sampleMeasure : Measure ℝ := volume.restrict (Icc (1 : ℝ) 2)

instance sampleMeasure_isFiniteMeasure : IsFiniteMeasure sampleMeasure :=
  isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; simp)

theorem sampleMeasure_univ : sampleMeasure univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]; norm_num

/-- The sampling Hilbert space. -/
abbrev SampleSpace := Lp ℂ 2 sampleMeasure

/-- The embedding of a function into `L²([1, 2])`; zero if the function is not square integrable. -/
def toSample (g : ℝ → ℂ) : SampleSpace :=
  if h : MemLp g 2 sampleMeasure then h.toLp g else 0

theorem toSample_eq {g : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure) : toSample g = hg.toLp g := by
  rw [toSample, dif_pos hg]

theorem coeFn_toSample {g : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure) :
    (toSample g : ℝ → ℂ) =ᵐ[sampleMeasure] g := by
  rw [toSample_eq hg]; exact hg.coeFn_toLp

/-- Bounded measurable functions are square integrable on `[1, 2]`. -/
theorem memLp_sample_of_bound {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g sampleMeasure) {C : ℝ}
    (hgb : ∀ u ∈ Icc (1 : ℝ) 2, ‖g u‖ ≤ C) : MemLp g 2 sampleMeasure := by
  refine MemLp.of_bound hgm C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall hgb

/-- Continuous functions on `[1, 2]` are square integrable there. -/
theorem memLp_sample_of_continuousOn {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (1 : ℝ) 2)) :
    MemLp g 2 sampleMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact memLp_sample_of_bound (hg.aestronglyMeasurable measurableSet_Icc) hC

/-- **The inner product formula.** -/
theorem inner_toSample {g k : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure)
    (hk : MemLp k 2 sampleMeasure) :
    (inner ℂ (toSample g) (toSample k) : ℂ) = ∫ u in Icc (1 : ℝ) 2, conj (g u) * k u := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toSample hg, coeFn_toSample hk] with u hu1 hu2
  rw [hu1, hu2]
  simp [mul_comm]

/-- **The norm bound.** -/
theorem norm_toSample_le {g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ u ∈ Icc (1 : ℝ) 2, ‖g u‖ ≤ C) : ‖toSample g‖ ≤ C := by
  by_cases hg : MemLp g 2 sampleMeasure
  · have hae : ∀ᵐ u ∂sampleMeasure, ‖(toSample g : ℝ → ℂ) u‖ ≤ C := by
      filter_upwards [coeFn_toSample hg, ae_restrict_mem measurableSet_Icc] with u hu hmem
      rw [hu]; exact hgb u hmem
    have := Lp.norm_le_of_ae_bound (p := 2) hC hae
    rw [measureUnivNNReal, sampleMeasure_univ] at this
    simpa using this
  · rw [toSample, dif_neg hg, norm_zero]; exact hC

theorem toSample_add {g k : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure)
    (hk : MemLp k 2 sampleMeasure) : toSample (g + k) = toSample g + toSample k := by
  rw [toSample_eq (hg.add hk), toSample_eq hg, toSample_eq hk, MemLp.toLp_add]

theorem toSample_sub {g k : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure)
    (hk : MemLp k 2 sampleMeasure) : toSample (g - k) = toSample g - toSample k := by
  rw [toSample_eq (hg.sub hk), toSample_eq hg, toSample_eq hk, MemLp.toLp_sub]

theorem toSample_smul (c : ℂ) {g : ℝ → ℂ} (hg : MemLp g 2 sampleMeasure) :
    toSample (c • g) = c • toSample g := by
  rw [toSample_eq (hg.const_smul c), toSample_eq hg, MemLp.toLp_const_smul]

theorem toSample_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, MemLp (g i) 2 sampleMeasure) :
    toSample (∑ i ∈ s, g i) = ∑ i ∈ s, toSample (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toSample, MemLp.zero, Lp.toLp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      toSample_add (hg a (Finset.mem_insert_self a s))
        (memLp_finset_sum' s fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- A.e. equality on `[1, 2]` of functions continuous there is equality on `[1, 2]`. -/
theorem eqOn_Icc_of_ae_eq {f g : ℝ → ℂ} (hf : ContinuousOn f (Icc (1 : ℝ) 2))
    (hg : ContinuousOn g (Icc (1 : ℝ) 2)) (h : f =ᵐ[sampleMeasure] g) :
    EqOn f g (Icc (1 : ℝ) 2) := by
  intro x hx
  by_contra hne
  have hne' : f x - g x ≠ 0 := sub_ne_zero.mpr hne
  have hcont : ContinuousOn (fun y => f y - g y) (Icc (1 : ℝ) 2) := hf.sub hg
  have hU : ∀ᶠ y in 𝓝[Icc (1 : ℝ) 2] x, f y - g y ≠ 0 := (hcont x hx).eventually_ne hne'
  obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.mp hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo x hxV
  set I := Ioo (max 1 (x - r)) (min 2 (x + r)) with hI
  have hx1 : (1 : ℝ) ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hIpos : max 1 (x - r) < min 2 (x + r) :=
    max_lt (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by linarith))
  have hIsub : I ⊆ {y | f y ≠ g y} ∩ Icc (1 : ℝ) 2 := by
    intro y hy
    have hyab : y ∈ Icc (1 : ℝ) 2 :=
      ⟨(le_max_left _ _).trans hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
    have hyball : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [(le_max_right (1 : ℝ) (x - r)).trans_lt hy.1]
      · linarith [hy.2.trans_le (min_le_right (2 : ℝ) (x + r))]
    exact ⟨fun heq => hVsub ⟨hball hyball, hyab⟩ (sub_eq_zero.mpr heq), hyab⟩
  have hzero : volume ({y | f y ≠ g y} ∩ Icc (1 : ℝ) 2) = 0 := by
    have := ae_iff.mp h
    rwa [Measure.restrict_apply' measurableSet_Icc] at this
  have hIvol : 0 < volume I := by rw [hI, Real.volume_Ioo]; simpa using hIpos
  exact absurd (measure_mono hIsub) (by rw [hzero]; exact not_le.mpr hIvol)

end RHTower
