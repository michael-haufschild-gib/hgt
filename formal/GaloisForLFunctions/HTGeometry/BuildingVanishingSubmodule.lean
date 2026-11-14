import GaloisForLFunctions.HTGeometry.FamilyBuildingVanishing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Solomon--Tits vanishing for the subspaces of a finite-dimensional vector space

The lattice of submodules of a finite-dimensional vector space is bounded, modular, atomic, and
graded by the dimension: a covering pair differs by one, because a proper extension of the smaller
by one vector already lies strictly between unless it is the larger.  So the general vanishing
theorem applies, and the order complex of the proper nonzero subspaces — the Tits building — has no
homology in degrees `1` through `dim V - 3`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u c

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The dimension of submodules is graded**: a covering pair differs by exactly one. -/
theorem finrank_of_covBy {U W : Submodule K V} (h : U ⋖ W) :
    finrank K W = finrank K U + 1 := by
  obtain ⟨x, hxW, hxU⟩ : ∃ x ∈ W, x ∉ U := SetLike.exists_of_lt h.1
  have hspan : Submodule.span K {x} ≤ W := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hxW
  have hlt : U < U ⊔ Submodule.span K {x} :=
    left_lt_sup.2 (fun hcon => hxU (hcon (Submodule.mem_span_singleton_self x)))
  have hnot := h.2 hlt
  have heq : U ⊔ Submodule.span K {x} = W :=
    (lt_or_eq_of_le (sup_le (le_of_lt h.1) hspan)).resolve_left hnot
  rw [← heq, Submodule.finrank_sup_span_singleton hxU]

section

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **Solomon--Tits vanishing for a vector space.**  The order complex of the proper nonzero
subspaces of a finite-dimensional vector space has no homology in degree `i` whenever
`1 ≤ i` and `i + 3 ≤ dim V`. -/
theorem isZero_homology_properPart_submodule [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hrank : i + 3 ≤ finrank K V) :
    Limits.IsZero ((nerve (properPart (Submodule K V))).homology R i) := by
  refine isZero_homology_properPart_of_rank (fun U : Submodule K V => finrank K U)
    (finrank_bot K V)
    (fun {U W} h => finrank_of_covBy h)
    (fun U hU => (eq_bot_or_exists_atom_le U).resolve_left (ne_of_gt hU)) R i hi
    bot_lt_top ?_
  rwa [finrank_top]

end

end GaloisForLFunctions.HTGeometry
