/-
# Physical-time transfer of a torus bound

A rationally independent phase flow equidistributes, so a continuous statistic has its Haar mean as
its long-time average.  An upper semicontinuous statistic is squeezed from above by continuous
majorants with almost the same Haar mean, so its upper time average is still at most its Haar mean:
the completed-time bound of a closed-target statistic never exceeds its torus integral.

Density of the same orbit turns a strict Haar bound into a syndetic one: the strict sublevel set is
open and nonempty, and a dense one-parameter subgroup of a compact group meets every nonempty open
set in every interval of one fixed length.

Main results:
* `finiteClockPhaseHom` — the phase flow as a one-parameter subgroup.
* `limsup_integral_phaseMeasure_le_of_upperSemicontinuous` — **the physical-time transfer**.
* `exists_syndetic_lt_of_upperSemicontinuous` — **the syndetic clause**.
-/
import GaloisForLFunctions.HTGeometry.FiniteSpectralRecurrenceFrequencyLaw
import GaloisForLFunctions.HTGeometry.PhaseOrbitClosureSubtorus
import GaloisForLFunctions.HTGeometry.SyndeticDenseOrbitLaw
import GaloisForLFunctions.HTGeometry.UpperSemicontinuousMajorant
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Transfer

variable {d : Type*} [Fintype d]

theorem integrable_of_bounded_measurable {mu : Measure (UnitAddTorus d)} [IsFiniteMeasure mu]
    {f : UnitAddTorus d → ℝ} (hmeas : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    Integrable f mu :=
  (MeasureTheory.integrable_const M).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- **The physical-time transfer.**  Along a rationally independent phase flow the upper limit of
the sampled-time average of an upper semicontinuous statistic is at most its Haar mean. -/
theorem limsup_integral_phaseMeasure_le_of_upperSemicontinuous
    (frequency : d → ℝ) (hind : RationallyIndependentFrequency frequency)
    {f : UnitAddTorus d → ℝ} (hf : UpperSemicontinuous f)
    (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M) :
    atTop.limsup (fun T => ∫ x, f x ∂(finiteTorusPhaseProbabilityMeasure frequency T :
        Measure (UnitAddTorus d)))
      ≤ ∫ x, f x ∂(volume : Measure (UnitAddTorus d)) := by
  classical
  have hmeas : Measurable f := hf.measurable
  have hM0 : (0 : ℝ) ≤ M := le_trans (h0 (Classical.arbitrary _)) (hM _)
  have habs : ∀ x, |f x| ≤ M := fun x => abs_le.mpr ⟨by linarith [h0 x, hM x], hM x⟩
  have hfint : ∀ mu : Measure (UnitAddTorus d), IsFiniteMeasure mu → Integrable f mu := by
    intro mu hmu
    exact integrable_of_bounded_measurable (mu := mu) hmeas habs
  have hlim := finiteTorusPhaseProbabilityMeasure_tendsto_haar frequency hind
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨g, hgc, hfg, hgM, hgint⟩ := exists_continuous_majorant hf h0 hM
    (volume : Measure (UnitAddTorus d)) (eps := eps / 2) (by linarith)
  have hgabs : ∀ x, |g x| ≤ M := fun x =>
    abs_le.mpr ⟨by linarith [h0 x, hfg x, hM0], hgM x⟩
  have hgconv : Tendsto (fun T => ∫ x, g x
      ∂(finiteTorusPhaseProbabilityMeasure frequency T : Measure (UnitAddTorus d))) atTop
      (𝓝 (∫ x, g x ∂(volume : Measure (UnitAddTorus d)))) := by
    have hbc := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
      (BoundedContinuousFunction.mkOfCompact ⟨g, hgc⟩)
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hbc
    exact hbc
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hgconv) (eps / 2) (by linarith)
  have hev : ∀ᶠ T in atTop, (∫ x, f x
      ∂(finiteTorusPhaseProbabilityMeasure frequency T : Measure (UnitAddTorus d)))
      ≤ (∫ x, f x ∂(volume : Measure (UnitAddTorus d))) + eps := by
    refine Filter.eventually_atTop.mpr ⟨T₀, fun T hT => ?_⟩
    have hmono : (∫ x, f x
        ∂(finiteTorusPhaseProbabilityMeasure frequency T : Measure (UnitAddTorus d)))
        ≤ ∫ x, g x
        ∂(finiteTorusPhaseProbabilityMeasure frequency T : Measure (UnitAddTorus d)) := by
      refine MeasureTheory.integral_mono
        (hfint _ inferInstance)
        (integrable_of_bounded_measurable hgc.measurable hgabs) ?_
      exact fun x => hfg x
    have hnear := hT₀ T hT
    rw [Real.dist_eq] at hnear
    have := (abs_lt.mp hnear).2
    linarith [hgint]
  refine Filter.limsup_le_of_le ?_ hev
  refine Filter.IsBoundedUnder.isCoboundedUnder_le ?_
  refine ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun T => ?_)⟩
  exact MeasureTheory.integral_nonneg (Pi.le_def.mpr h0)

end Transfer


section Syndetic

variable {d : Type*} [Fintype d]

/-- The phase flow as a one-parameter subgroup of the phase torus. -/
def finiteClockPhaseHom (omega : d → ℝ) : ℝ →+ UnitAddTorus d where
  toFun := finiteClockPhasePoint omega
  map_zero' := by
    funext i
    show ((0 * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle) = 0
    norm_num
  map_add' s t := by
    funext i
    show (((s + t) * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)
        = ((s * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)
          + ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)
    rw [← QuotientAddGroup.mk_add]
    congr 1
    ring

/-- **The syndetic clause.**  If an upper semicontinuous statistic dips below a level somewhere on
the torus, then along a rationally independent phase flow it dips below that level in every
interval of one fixed finite length. -/
theorem exists_syndetic_lt_of_upperSemicontinuous
    (frequency : d → ℝ) (hind : RationallyIndependentFrequency frequency)
    {f : UnitAddTorus d → ℝ} (hf : UpperSemicontinuous f) {theta : ℝ}
    (hne : ∃ x, f x < theta) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ t ∈ Icc a (a + L), f (finiteClockPhasePoint frequency t) < theta := by
  have hopen : IsOpen {x : UnitAddTorus d | f x < theta} := hf.isOpen_preimage theta
  have hdense : DenseRange (finiteClockPhaseHom frequency) :=
    dense_range_finiteClockPhasePoint frequency hind
  obtain ⟨L, hL0, hLall⟩ := denseAddOrbit_open_hits_syndetically
    (finiteClockPhaseHom frequency) hdense hopen hne
  exact ⟨L, hL0, hLall⟩

/-- A statistic whose Haar mean is below a level dips below it somewhere. -/
theorem exists_lt_of_integral_lt {f : UnitAddTorus d → ℝ} (hf : UpperSemicontinuous f)
    (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M) {theta : ℝ}
    (hmean : ∫ x, f x ∂(volume : Measure (UnitAddTorus d)) < theta) :
    ∃ x, f x < theta := by
  by_contra hcon
  have hcon' : ∀ x, theta ≤ f x := fun x => le_of_not_gt (fun h => hcon ⟨x, h⟩)
  have hmeas : Measurable f := hf.measurable
  have habs : ∀ x, |f x| ≤ M := fun x => abs_le.mpr ⟨by linarith [h0 x, hM x], hM x⟩
  have hint : Integrable f (volume : Measure (UnitAddTorus d)) :=
    integrable_of_bounded_measurable hmeas habs
  have hge : theta ≤ ∫ x, f x ∂(volume : Measure (UnitAddTorus d)) := by
    have hprob : (volume : Measure (UnitAddTorus d)) Set.univ = 1 := by
      rw [← finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
      exact measure_univ
    have hconst : ∫ _ : UnitAddTorus d, theta ∂(volume : Measure (UnitAddTorus d)) = theta := by
      rw [MeasureTheory.integral_const, measureReal_def, hprob]
      simp
    rw [← hconst]
    exact MeasureTheory.integral_mono (MeasureTheory.integrable_const theta) hint (Pi.le_def.mpr hcon')
  linarith

end Syndetic

end GaloisForLFunctions.HTGeometry

end
