import GaloisForLFunctions.HTGeometry.UniformNodeChoiceGenericity
import Mathlib.Topology.Compactness.Compact

/-!
# Openness of a condition quantified over a compact patch of shifts

The full rank witness quantifies over shifts before choosing a packet, so the condition on a density
is an intersection over an uncountable shift family.  Restricted to a compact patch of shifts, that
intersection is still an open condition.

The reason is the tube lemma: the densities failing at some shift of the patch are the projection of
a closed set along a compact factor, and such a projection is closed.  This is what makes a compact
exhaustion of the shift space usable where the raw uncountable quantifier is not.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A closed condition quantified over a compact patch is open in the parameter.**  If the failure
locus is closed jointly in parameter and shift, then the parameters succeeding at every shift of a
compact patch form an open set. -/
theorem isOpen_setOf_forall_mem_compact_notMem
    {X S : Type*} [TopologicalSpace X] [TopologicalSpace S]
    {A : Set (X × S)} (hA : IsClosed A) {K : Set S} (hK : IsCompact K) :
    IsOpen {x : X | ∀ s ∈ K, (x, s) ∉ A} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hsub : ({x} : Set X) ×ˢ K ⊆ Aᶜ := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx s hs
  obtain ⟨u, v, hu, _hv, hxu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hA.isOpen_compl hsub
  refine ⟨u, ?_, hu, hxu (Set.mem_singleton x)⟩
  intro y hy s hs
  exact huv ⟨hy, hKv hs⟩

/-- The failure locus of a family of conditions is closed when each member is. -/
theorem isClosed_setOf_forall_zero
    {X S ζ : Type*} [TopologicalSpace X] [TopologicalSpace S]
    (f : ζ → X × S → ℂ) (hf : ∀ c, Continuous (f c)) :
    IsClosed {p : X × S | ∀ c, f c p = 0} := by
  have hset : {p : X × S | ∀ c, f c p = 0} = ⋂ c, (f c) ⁻¹' {0} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  exact isClosed_iInter fun c => isClosed_singleton.preimage (hf c)

/-- **Openness of the patchwise witness condition.**  If for each choice of data the vanishing locus
is closed jointly in parameter and shift, then the parameters admitting, at every shift of a compact
patch, some datum with nonvanishing value form an open set. -/
theorem isOpen_setOf_forall_compact_exists_ne_zero
    {X S ζ : Type*} [TopologicalSpace X] [TopologicalSpace S]
    (f : ζ → X × S → ℂ) (hf : ∀ c, Continuous (f c))
    {K : Set S} (hK : IsCompact K) :
    IsOpen {x : X | ∀ s ∈ K, ∃ c, f c (x, s) ≠ 0} := by
  have hA := isClosed_setOf_forall_zero f hf
  have hset : {x : X | ∀ s ∈ K, ∃ c, f c (x, s) ≠ 0} =
      {x : X | ∀ s ∈ K, (x, s) ∉ {p : X × S | ∀ c, f c p = 0}} := by
    ext x
    simp only [Set.mem_setOf_eq, not_forall]
  rw [hset]
  exact isOpen_setOf_forall_mem_compact_notMem hA hK

end

end GaloisForLFunctions.HTGeometry
