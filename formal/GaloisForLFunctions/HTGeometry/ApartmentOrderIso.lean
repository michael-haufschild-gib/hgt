import GaloisForLFunctions.HTGeometry.BuildingVanishingDual
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The apartment of an observer frame is a Boolean lattice

A basis of the space — a projective observer frame — spans a coordinate subspace for every set of
its members, and that assignment is an order embedding of the lattice of subsets: it is monotone,
and it reflects the order because a basis vector outside a set is not in the span of that set.

So the coordinate subspaces of a frame form a sublattice of the subspaces isomorphic to the lattice
of subsets, and the proper nonzero ones — the vertices of the apartment — form a poset isomorphic to
the proper part of that Boolean lattice.  The apartment's order complex is therefore the order
complex of the proper part of a Boolean lattice, which is the Coxeter sphere the card names.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

universe u

variable {K V ι : Type u} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The coordinate subspace spanned by a set of frame vectors. -/
def coordSpan (b : Basis ι K V) (s : Set ι) : Submodule K V := Submodule.span K (b '' s)

theorem coordSpan_mono (b : Basis ι K V) : Monotone (coordSpan b) := fun _ _ h =>
  Submodule.span_mono (Set.image_mono h)

/-- **The frame's coordinate subspaces reflect inclusion.**  A frame vector outside a set is not in
the span of that set. -/
theorem coordSpan_le_iff (b : Basis ι K V) (s t : Set ι) :
    coordSpan b s ≤ coordSpan b t ↔ s ⊆ t := by
  refine ⟨fun h i his => ?_, fun h => coordSpan_mono b h⟩
  by_contra hit
  refine b.linearIndependent.notMem_span_image hit (h ?_)
  exact Submodule.subset_span (Set.mem_image_of_mem _ his)

/-- **The apartment of a frame**: the lattice of subsets embeds in the subspaces. -/
def apartmentEmbedding (b : Basis ι K V) : Set ι ↪o Submodule K V :=
  OrderEmbedding.ofMapLEIff (coordSpan b) (coordSpan_le_iff b)

theorem coordSpan_empty (b : Basis ι K V) : coordSpan b ∅ = ⊥ := by
  rw [coordSpan, Set.image_empty, Submodule.span_empty]

theorem coordSpan_univ (b : Basis ι K V) : coordSpan b Set.univ = ⊤ := by
  rw [coordSpan, Set.image_univ, ← Basis.span_eq b]

theorem coordSpan_injective (b : Basis ι K V) : Function.Injective (coordSpan b) := fun s t h =>
  Set.Subset.antisymm ((coordSpan_le_iff b s t).1 (le_of_eq h))
    ((coordSpan_le_iff b t s).1 (le_of_eq h.symm))

theorem coordSpan_ne_bot (b : Basis ι K V) {s : Set ι} (hs : s.Nonempty) : coordSpan b s ≠ ⊥ := by
  intro hcon
  rw [← coordSpan_empty b] at hcon
  exact absurd (coordSpan_injective b hcon) (Set.Nonempty.ne_empty hs)

theorem coordSpan_ne_top (b : Basis ι K V) {s : Set ι} (hs : s ≠ Set.univ) :
    coordSpan b s ≠ ⊤ := by
  intro hcon
  rw [← coordSpan_univ b] at hcon
  exact hs (coordSpan_injective b hcon)

/-- **The vertices of an apartment are the proper part of a Boolean lattice.**  A nonempty proper
set of frame vectors spans a proper nonzero subspace, and that assignment is an order isomorphism
onto its range. -/
def apartmentVertices (b : Basis ι K V) : properPart (Set ι) →o properPart (Submodule K V) where
  toFun s :=
    ⟨coordSpan b (s : Set ι),
      lt_of_le_of_ne bot_le (Ne.symm (coordSpan_ne_bot b
        (Set.nonempty_iff_ne_empty.2 (fun hcon => absurd (hcon ▸ s.2.1) (lt_irrefl _))))),
      lt_of_le_of_ne le_top (coordSpan_ne_top b (fun hcon => absurd (hcon ▸ s.2.2)
        (lt_irrefl _)))⟩
  monotone' _ _ h := coordSpan_mono b h

theorem apartmentVertices_le_iff (b : Basis ι K V) (s t : properPart (Set ι)) :
    apartmentVertices b s ≤ apartmentVertices b t ↔ s ≤ t :=
  coordSpan_le_iff b (s : Set ι) (t : Set ι)

/-! ## The apartment's own homology -/

section Boolean

variable {ι : Type u} [Fintype ι]

/-- **Subsets are graded by cardinality**: a covering pair differs by one element. -/
theorem ncard_of_covBy {s t : Set ι} (h : s ⋖ t) : t.ncard = s.ncard + 1 := by
  obtain ⟨a, hat, has⟩ : ∃ a, a ∈ t ∧ a ∉ s := by
    by_contra hcon
    push Not at hcon
    exact absurd (Set.Subset.antisymm (fun x hx => hcon x hx) (le_of_lt h.1))
      (ne_of_lt h.1).symm
  have hins : insert a s ⊆ t := Set.insert_subset hat (le_of_lt h.1)
  have heq : insert a s = t := by
    rcases eq_or_lt_of_le hins with h' | h'
    · exact h'
    · exact absurd h' (h.2 (Set.ssubset_insert has))
  rw [← heq, Set.ncard_insert_of_notMem has (Set.toFinite s)]

section

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- **The apartment has no homology below its top degree.**  The subsets of a frame form a Boolean
lattice, which is modular, atomic and graded by cardinality, so the Solomon--Tits vanishing applies
to it verbatim: the Coxeter sphere has nothing below the top. -/
theorem isZero_homology_properPart_set [Nonempty ι] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hrank : i + 3 ≤ Nat.card ι) :
    Limits.IsZero ((nerve (properPart (Set ι))).homology R i) := by
  refine isZero_homology_properPart_of_rank (fun s : Set ι => s.ncard) (Set.ncard_empty ι)
    (fun {s t} h => ncard_of_covBy h) ?_ R i hi ?_ ?_
  · intro s hs
    obtain ⟨a, ha⟩ : s.Nonempty :=
      Set.nonempty_iff_ne_empty.2 (fun hcon => absurd (hcon ▸ hs) (lt_irrefl _))
    exact ⟨{a}, Set.isAtom_singleton a, Set.singleton_subset_iff.2 ha⟩
  · exact Set.empty_ssubset.2 Set.univ_nonempty
  · show i + 3 ≤ (Set.univ : Set ι).ncard
    rw [Set.ncard_univ]
    exact hrank

end

end Boolean

end GaloisForLFunctions.HTGeometry
