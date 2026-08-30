import Mathlib

/-!
# Prevalence

A set in a topological additive group is *prevalent* when one compactly supported probability
measure — a probe — makes its complement null after every deterministic recentring.  This is the
measure-theoretic analogue of comeagreness on an infinite-dimensional space, where no translation
invariant measure exists.  Only the complement-null form is used, so no measurability of the tested
set is required anywhere.
-/

open MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

/-- A compactly supported probability measure. -/
structure CompactProbe (E : Type*) [TopologicalSpace E] [MeasurableSpace E] where
  /-- The underlying law. -/
  measure : Measure E
  /-- It is a probability measure. -/
  isProbability : IsProbabilityMeasure measure
  /-- A compact carrier. -/
  carrier : Set E
  /-- The carrier is compact. -/
  isCompact_carrier : IsCompact carrier
  /-- The carrier is full. -/
  measure_compl_carrier : measure carrierᶜ = 0

attribute [instance] CompactProbe.isProbability

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [MeasurableSpace E]

/-- `G` is **prevalent on `B`** when a single compact probe makes the complement of `G` null after
every deterministic recentring inside `B`. -/
def PrevalentOn (B G : Set E) : Prop :=
  ∃ P : CompactProbe E, ∀ x ∈ B, P.measure {w | x + w ∉ G} = 0

/-- `G` is **prevalent** when it is prevalent on the whole space. -/
def Prevalent (G : Set E) : Prop := PrevalentOn (Set.univ : Set E) G

theorem prevalent_iff (G : Set E) :
    Prevalent G ↔ ∃ P : CompactProbe E, ∀ x : E, P.measure {w | x + w ∉ G} = 0 := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, fun x => hP x (Set.mem_univ x)⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, fun x _ => hP x⟩

/-- Prevalence is inherited by supersets. -/
theorem PrevalentOn.mono {B G G' : Set E} (h : PrevalentOn B G) (hGG' : G ⊆ G') :
    PrevalentOn B G' := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun x hx => ?_⟩
  refine measure_mono_null (fun w hw => ?_) (hP x hx)
  exact fun hmem => hw (hGG' hmem)

/-- Prevalence on a smaller recentring set. -/
theorem PrevalentOn.subset {B B' G : Set E} (h : PrevalentOn B G) (hB : B' ⊆ B) :
    PrevalentOn B' G := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun x hx => hP x (hB hx)⟩

/-- **A countable intersection tested by one probe is prevalent.** -/
theorem prevalentOn_iInter {ι : Type*} [Countable ι] {B : Set E} {G : ι → Set E}
    (P : CompactProbe E) (h : ∀ i, ∀ x ∈ B, P.measure {w | x + w ∉ G i} = 0) :
    PrevalentOn B (⋂ i, G i) := by
  refine ⟨P, fun x hx => ?_⟩
  have hcover : {w : E | x + w ∉ ⋂ i, G i} = ⋃ i, {w : E | x + w ∉ G i} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    push Not
    rfl
  rw [hcover]
  exact measure_iUnion_null fun i => h i x hx

/-- The pushforward of a compact probe under a continuous measurable map is a compact probe. -/
noncomputable def CompactProbe.map {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [T2Space F] [OpensMeasurableSpace F]
    (P : CompactProbe E) (f : E → F)
    (hf : Continuous f) (hfm : Measurable f) : CompactProbe F where
  measure := Measure.map f P.measure
  isProbability := Measure.isProbabilityMeasure_map hfm.aemeasurable
  carrier := f '' P.carrier
  isCompact_carrier := P.isCompact_carrier.image hf
  measure_compl_carrier := by
    have hmeas : MeasurableSet ((f '' P.carrier)ᶜ) :=
      ((P.isCompact_carrier.image hf).isClosed.measurableSet).compl
    rw [Measure.map_apply hfm hmeas]
    refine measure_mono_null (fun w hw => ?_) P.measure_compl_carrier
    intro hwc
    exact hw (Set.mem_image_of_mem f hwc)

@[simp] theorem CompactProbe.map_measure {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [T2Space F] [OpensMeasurableSpace F]
    (P : CompactProbe E) (f : E → F)
    (hf : Continuous f) (hfm : Measurable f) :
    (P.map f hf hfm).measure = Measure.map f P.measure := rfl

/-- The uniform probe on a cube: normalized Lebesgue measure on a closed sup-norm ball. -/
noncomputable def cubeProbe (d : ℕ) {a : ℝ} (ha : 0 < a) : CompactProbe (Fin d → ℝ) where
  measure := (volume (Metric.closedBall (0 : Fin d → ℝ) a))⁻¹ •
    volume.restrict (Metric.closedBall (0 : Fin d → ℝ) a)
  isProbability := by
    constructor
    have hpos : 0 < volume (Metric.closedBall (0 : Fin d → ℝ) a) :=
      measure_closedBall_pos volume 0 ha
    have hlt : volume (Metric.closedBall (0 : Fin d → ℝ) a) < ⊤ :=
      (isCompact_closedBall (0 : Fin d → ℝ) a).measure_lt_top
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hpos.ne' hlt.ne
  carrier := Metric.closedBall (0 : Fin d → ℝ) a
  isCompact_carrier := isCompact_closedBall (0 : Fin d → ℝ) a
  measure_compl_carrier := by
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply₀' measurableSet_closedBall.nullMeasurableSet,
      Set.compl_inter_self, measure_empty, mul_zero]

theorem cubeProbe_absolutelyContinuous (d : ℕ) {a : ℝ} (ha : 0 < a) :
    (cubeProbe d ha).measure ≪ (volume : Measure (Fin d → ℝ)) := by
  intro s hs
  show ((volume (Metric.closedBall (0 : Fin d → ℝ) a))⁻¹ •
    volume.restrict (Metric.closedBall (0 : Fin d → ℝ) a)) s = 0
  rw [Measure.smul_apply, smul_eq_mul]
  have hz : volume.restrict (Metric.closedBall (0 : Fin d → ℝ) a) s = 0 := by
    rw [Measure.restrict_apply₀' measurableSet_closedBall.nullMeasurableSet]
    exact measure_mono_null Set.inter_subset_left hs
  rw [hz, mul_zero]

end GaloisForLFunctions.HTGeometry
