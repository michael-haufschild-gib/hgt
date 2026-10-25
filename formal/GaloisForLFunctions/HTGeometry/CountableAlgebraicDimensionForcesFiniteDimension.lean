import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Countable algebraic dimension in a Banach space

Baire category forces a countably spanned Banach space to be finite-dimensional.
Consequently its Hamel dimension is finite or uncountable.
-/

noncomputable section
set_option autoImplicit false
open Set

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A countable algebraic cover of a Banach space by finite-dimensional subspaces
contains the whole space as one member. -/
theorem exists_eq_top_of_countable_finiteDimensional_cover {ι : Type*} [Countable ι]
    (V : ι → Submodule ℂ E) [∀ i, FiniteDimensional ℂ (V i)]
    (hcover : (⋃ i, (V i : Set E)) = Set.univ) : ∃ i, V i = ⊤ := by
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed
    (fun i => (V i).closed_of_finiteDimensional) hcover
  exact ⟨i, (V i).eq_top_of_nonempty_interior' hi⟩

/-- A Banach space with a countable algebraic spanning family is finite-dimensional. -/
theorem finiteDimensional_of_countable_algebraic_span {ι : Type*} [Countable ι]
    (v : ι → E) (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    FiniteDimensional ℂ E := by
  classical
  let V (s : Finset ι) : Submodule ℂ E := Submodule.span ℂ (v '' (s : Set ι))
  haveI (s : Finset ι) : FiniteDimensional ℂ (V s) :=
    FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image v)
  have hmem : ∀ x : E, ∃ s : Finset ι, x ∈ V s := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨{i}, Submodule.subset_span ?_⟩
      exact ⟨i, by simp, rfl⟩
    | zero => exact ⟨∅, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, Submodule.add_mem _ ?_ ?_⟩
      · exact (Submodule.span_mono (Set.image_mono (by simp)) : V s ≤ V (s ∪ t)) hs
      · exact (Submodule.span_mono (Set.image_mono (by simp)) : V t ≤ V (s ∪ t)) ht
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨s, Submodule.smul_mem _ c hs⟩
  have hcover : (⋃ s, (V s : Set E)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hmem x
  obtain ⟨s, hs⟩ := exists_eq_top_of_countable_finiteDimensional_cover V hcover
  apply FiniteDimensional.of_surjective (V s).subtype
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [hs]
  trivial

/-- Countable algebraic dimension forces finite dimension in a Banach space. -/
theorem finiteDimensional_of_rank_le_aleph0
    (hrank : Module.rank ℂ E ≤ Cardinal.aleph0) : FiniteDimensional ℂ E := by
  haveI : Countable (Module.Free.ChooseBasisIndex ℂ E) := by
    apply Cardinal.mk_le_aleph0_iff.mp
    rw [← Module.Free.rank_eq_card_chooseBasisIndex]
    exact hrank
  exact finiteDimensional_of_countable_algebraic_span (Module.Free.chooseBasis ℂ E)
    (Module.Free.chooseBasis ℂ E).span_eq

/-- A Banach space cannot have countably infinite algebraic dimension. -/
theorem banach_rank_ne_aleph0 : Module.rank ℂ E ≠ Cardinal.aleph0 := by
  intro hrank
  haveI : FiniteDimensional ℂ E := finiteDimensional_of_rank_le_aleph0 hrank.le
  exact (Module.rank_lt_aleph0 ℂ E).ne hrank

/-- Every Banach space has finite or uncountable algebraic dimension. -/
theorem banach_finite_or_uncountable :
    FiniteDimensional ℂ E ∨ Cardinal.aleph0 < Module.rank ℂ E := by
  by_cases h : Module.rank ℂ E ≤ Cardinal.aleph0
  · exact Or.inl (finiteDimensional_of_rank_le_aleph0 h)
  · exact Or.inr (lt_of_not_ge h)

end GaloisForLFunctions.HTGeometry
