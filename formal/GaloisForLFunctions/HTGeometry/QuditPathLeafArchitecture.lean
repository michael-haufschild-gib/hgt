import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# Adjoining one leaf at the end of a path is the next path

The interaction graph of a leaf extension attached at the last vertex of an open path is the open
path with one more vertex.  This is the architecture bookkeeping behind the chain law: the whole
chain is one leaf extension of the chain one site shorter.

## Main results

* `leafPathEquiv` — the relabelling of the leaf-extended observer set.
* `leafGraphExtension_comap_pathGraph` — the graph identity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Relabel a leaf-extended observer set as the vertices of the next path. -/
def leafPathEquiv {S : Type u} {m : ℕ} (e : S ≃ Fin m) :
    LeafExtendedObserver S ≃ Fin (m + 1) where
  toFun := Sum.elim (fun x => (e x).castSucc) (fun _ => Fin.last m)
  invFun := fun i => if h : (i : ℕ) < m then Sum.inl (e.symm ⟨i, h⟩) else Sum.inr ()
  left_inv := by
    rintro (x | u)
    · simp
    · simp
  right_inv := by
    intro i
    by_cases h : (i : ℕ) < m
    · simp only [h, dif_pos, Sum.elim_inl, Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · have hi : (i : ℕ) = m := by omega
      simp only [h, dif_neg, not_false_iff, Sum.elim_inr]
      exact Fin.ext (by simp [Fin.last, hi])

/-- **Adjoining one leaf at the last vertex of a path gives the next path.** -/
theorem leafGraphExtension_comap_pathGraph {S : Type u} {m : ℕ}
    (e : S ≃ Fin m) (root : S) (hroot : ((e root : Fin m) : ℕ) + 1 = m) :
    leafGraphExtension (SimpleGraph.comap e (SimpleGraph.pathGraph m)) root
      = SimpleGraph.comap (leafPathEquiv e) (SimpleGraph.pathGraph (m + 1)) := by
  ext a b
  rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj, leafGraphExtension,
    SimpleGraph.fromRel_adj]
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          simp only [leafPathEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Fin.val_castSucc,
            SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj, ne_eq, Sum.inl.injEq]
          constructor
          · rintro ⟨-, h | h⟩
            · exact h
            · exact h.symm
          · intro h
            refine ⟨?_, Or.inl h⟩
            intro hxy
            subst hxy
            omega
      | inr u =>
          have hx : ((e x : Fin m) : ℕ) < m := (e x).2
          simp only [leafPathEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
            Fin.val_castSucc, Fin.val_last, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
            or_self]
          constructor
          · rintro rfl
            exact Or.inl hroot
          · intro h
            have hval : ((e x : Fin m) : ℕ) = ((e root : Fin m) : ℕ) := by omega
            exact e.injective (Fin.ext hval)
  | inr u =>
      cases b with
      | inl y =>
          have hy : ((e y : Fin m) : ℕ) < m := (e y).2
          simp only [leafPathEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
            Fin.val_castSucc, Fin.val_last, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
            or_self]
          constructor
          · rintro rfl
            exact Or.inr hroot
          · intro h
            have hval : ((e y : Fin m) : ℕ) = ((e root : Fin m) : ℕ) := by omega
            exact e.injective (Fin.ext hval)
      | inr v =>
          simp only [leafPathEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Fin.val_last, ne_eq,
            or_self, and_false, false_iff]
          omega

end

end GaloisForLFunctions.HTGeometry
