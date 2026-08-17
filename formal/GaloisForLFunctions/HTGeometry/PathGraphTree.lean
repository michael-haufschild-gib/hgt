import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Finite path graphs are trees
-/

namespace SimpleGraph

/-- Consecutive vertices determine an edge of the path on `n + 1` vertices. -/
def pathGraphEdge (n : ℕ) (i : Fin n) : (pathGraph (n + 1)).edgeSet :=
  ⟨s(i.castSucc, i.succ), by simp [pathGraph_adj]⟩

theorem pathGraphEdge_injective (n : ℕ) : Function.Injective (pathGraphEdge n) := by
  intro i j hij
  have hval : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) := congrArg Subtype.val hij
  rw [Sym2.eq_iff] at hval
  rcases hval with hdir | hswap
  · exact Fin.ext (by simpa using congrArg Fin.val hdir.1)
  · have h₁ := congrArg Fin.val hswap.1
    have h₂ := congrArg Fin.val hswap.2
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega

theorem pathGraphEdge_surjective (n : ℕ) : Function.Surjective (pathGraphEdge n) := by
  intro e
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro u v huv
  rw [mem_edgeSet, pathGraph_adj] at huv
  rcases huv with huv | huv
  · let i : Fin n := ⟨u.val, by omega⟩
    refine ⟨i, Subtype.ext ?_⟩
    simp only [pathGraphEdge, i]
    apply Sym2.eq_iff.mpr
    left
    exact ⟨Fin.ext rfl, Fin.ext (by simpa using huv)⟩
  · let i : Fin n := ⟨v.val, by omega⟩
    refine ⟨i, Subtype.ext ?_⟩
    simp only [pathGraphEdge, i]
    apply Sym2.eq_iff.mpr
    right
    exact ⟨Fin.ext rfl, Fin.ext (by simpa using huv)⟩

noncomputable def pathGraphEdgeEquiv (n : ℕ) :
    Fin n ≃ (pathGraph (n + 1)).edgeSet :=
  Equiv.ofBijective (pathGraphEdge n)
    ⟨pathGraphEdge_injective n, pathGraphEdge_surjective n⟩

/-- Every nonempty finite path graph is a tree. -/
theorem pathGraph_isTree (n : ℕ) : (pathGraph (n + 1)).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected n, ?_⟩
  rw [Nat.card_congr (pathGraphEdgeEquiv n).symm]
  simp

end SimpleGraph
