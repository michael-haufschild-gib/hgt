import Mathlib.Topology.Continuous

/-!
# Source-pointed strict descent law

Exact range realization and approximation are different transport invariants.  A continuous
consumer sends an approximable source value to an approximable output value.  If that consumer is
also injective, it reflects exact range membership.  Consequently a point in `closure(range) \
range` stays in `closure(range) \ range` after every continuous injective downstream consumer.

This is the topological irreversibility law complementary to kernel-pair monotonicity.  An
injective consumer can retain a closure-only boundary value, but it cannot manufacture the source
primitive that failed to exist upstream.
-/

open Function Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- An injective downstream consumer reflects exact membership in the upstream range. -/
theorem mem_range_comp_iff_of_injective
    {X Y Z : Type*} (T : X → Y) (J : Y → Z)
    (hJ : Function.Injective J) (y : Y) :
    J y ∈ Set.range (J ∘ T) ↔ y ∈ Set.range T := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, hJ ?_⟩
    simpa only [Function.comp_apply] using hx
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- A continuous downstream consumer preserves closure admission of an upstream range value. -/
theorem mem_closure_range_comp_of_continuous
    {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (T : X → Y) (J : Y → Z) (hJ : Continuous J) {y : Y}
    (hy : y ∈ closure (Set.range T)) :
    J y ∈ closure (Set.range (J ∘ T)) := by
  have himage : J y ∈ closure (J '' Set.range T) := by
    apply image_closure_subset_closure_image hJ
    exact ⟨y, hy, rfl⟩
  have hrange : J '' Set.range T = Set.range (J ∘ T) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨T x, ⟨x, rfl⟩, rfl⟩
  rwa [hrange] at himage

/-- **Closure-only persistence.**  Continuous injective postprocessing preserves exact
nonattainment as well as approximation. -/
theorem continuous_injective_consumer_preserves_closureOnly
    {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (T : X → Y) (J : Y → Z) (hJcont : Continuous J)
    (hJinj : Function.Injective J) {y : Y}
    (hyClosure : y ∈ closure (Set.range T))
    (hyNotRange : y ∉ Set.range T) :
    J y ∈ closure (Set.range (J ∘ T)) ∧
      J y ∉ Set.range (J ∘ T) := by
  refine ⟨mem_closure_range_comp_of_continuous T J hJcont hyClosure, ?_⟩
  rwa [mem_range_comp_iff_of_injective T J hJinj y]

/-- A law imposed on every primitive of a surjective transport is already a law on the whole
target.  Surjective strictification therefore cannot select a proper purity locus without an
additional source-sector restriction. -/
theorem target_law_of_forall_source_of_surjective
    {X Y : Type*} (T : X → Y) (hT : Function.Surjective T)
    (P : Y → Prop) (hP : ∀ x : X, P (T x)) :
    ∀ y : Y, P y := by
  intro y
  obtain ⟨x, rfl⟩ := hT y
  exact hP x

/-- Contrapositive selection form: if a target property fails somewhere, every surjective
transport has a source primitive on which it fails. -/
theorem exists_source_not_target_law_of_surjective
    {X Y : Type*} (T : X → Y) (hT : Function.Surjective T)
    (P : Y → Prop) (hP : ∃ y : Y, ¬ P y) :
    ∃ x : X, ¬ P (T x) := by
  obtain ⟨y, hy⟩ := hP
  obtain ⟨x, rfl⟩ := hT y
  exact ⟨x, hy⟩

end GaloisForLFunctions.HTGeometry
