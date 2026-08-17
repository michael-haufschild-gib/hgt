import GaloisForLFunctions.HTGeometry.CoherenceFlatness
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Prescribed Boolean edge orientations on trees

Every symmetric Boolean labeling of the edges of a tree is a vertex coboundary.  This is the
finite-characteristic-two form of the elementary fact that a tree has no cycle obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

universe u
variable {V : Type u}

theorem walkXor_concat {G : SimpleGraph V} (c : V → V → Bool)
    {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    walkXor c (p.concat h) = Bool.xor (walkXor c p) (c v w) := by
  rw [SimpleGraph.Walk.concat_eq_append, walkXor_append]
  simp

/-- A prescribed symmetric Boolean edge field on a tree integrates to vertex labels. -/
theorem exists_booleanOrientation_of_isTree
    {G : SimpleGraph V} (hG : G.IsTree) (c : V → V → Bool)
    (hsymm : BooleanEdgeFieldSymmetric G c) :
    ∃ ε : V → Bool, ∀ ⦃u v⦄, G.Adj u v →
      c u v = Bool.xor (ε u) (ε v) := by
  classical
  let root : V := Classical.choice hG.connected.nonempty
  let path : ∀ v : V, G.Path root v := fun v =>
    ⟨Classical.choose (hG.existsUnique_path root v),
      (Classical.choose_spec (hG.existsUnique_path root v)).1⟩
  let ε : V → Bool := fun v => walkXor c (path v : G.Walk root v)
  refine ⟨ε, ?_⟩
  intro u v huv
  by_cases hu : u ∈ (path v : G.Walk root v).support
  · have heq : (path v : G.Walk root v) =
        (path u : G.Walk root u).concat huv := by
      exact hG.isAcyclic.path_concat (path u).isPath (path v).isPath huv hu
    have hεv : ε v = Bool.xor (ε u) (c u v) := by
      change walkXor c (path v : G.Walk root v) =
        Bool.xor (walkXor c (path u : G.Walk root u)) (c u v)
      rw [heq, walkXor_concat]
    cases hcu : c u v <;> cases heu : ε u <;> cases hev : ε v <;> simp_all
  · have hv : v ∈ (path u : G.Walk root u).support :=
      hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (path u).isPath (path v).isPath huv hu
    have heq : (path u : G.Walk root u) =
        (path v : G.Walk root v).concat huv.symm := by
      exact hG.isAcyclic.path_concat (path v).isPath (path u).isPath huv.symm hv
    have hεu : ε u = Bool.xor (ε v) (c v u) := by
      change walkXor c (path u : G.Walk root u) =
        Bool.xor (walkXor c (path v : G.Walk root v)) (c v u)
      rw [heq, walkXor_concat]
    have hsymm' : c v u = c u v := hsymm huv.symm
    cases hcu : c u v <;> cases hcvu : c v u <;>
      cases heu : ε u <;> cases hev : ε v <;> simp_all

end GaloisForLFunctions.HTGeometry
