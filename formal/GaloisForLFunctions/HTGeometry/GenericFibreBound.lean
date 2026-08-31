import GaloisForLFunctions.HTGeometry.FibreSemicontinuity

/-!
# The generic fibre is no bigger than the special one

```text
finrank_fibre_one_le_zero   ** if all nonzero fibres agree, the fibre at one is at most the fibre
                               at zero **
```

The two facts about a finitely generated module over the base line — every fibre has at least the
rank, all but finitely many have exactly the rank — combine with an infinite field: some nonzero
point avoids the exceptional set, so the common nonzero-fibre value *is* the rank, which is a lower
bound for every fibre including the one at zero.

This is the fibre bound a degeneration argument consumes.  The hypothesis "all nonzero fibres agree"
is supplied by the rescaling `eval_homogenize`, which carries the fibre at any nonzero point
isomorphically onto the fibre at one.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

/-- **The fibre at one is no bigger than the fibre at zero**, once all nonzero fibres agree. -/
theorem finrank_fibre_one_le_zero [Infinite K] {V : Type*} [AddCommGroup V] [Module K[X] V]
    [Module K V] [IsScalarTower K K[X] V] [Module.Finite K[X] V]
    (hconst : ∀ lam : K, lam ≠ 0 →
      finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))
        = finrank K (V ⧸ (Ideal.span {(X - C (1 : K) : K[X])} • (⊤ : Submodule K[X] V)))) :
    finrank K (V ⧸ (Ideal.span {(X - C (1 : K) : K[X])} • (⊤ : Submodule K[X] V)))
      ≤ finrank K (V ⧸ (Ideal.span {(X - C (0 : K) : K[X])} • (⊤ : Submodule K[X] V))) := by
  classical
  obtain ⟨r, S, hge, heq⟩ := exists_generic_fibre_rank (K := K) (V := V)
  have hfin : ((↑S : Set K) ∪ {(0 : K)}).Finite :=
    (S.finite_toSet).union (Set.finite_singleton (0 : K))
  obtain ⟨lam, hlam⟩ := hfin.infinite_compl.nonempty
  have hlamS : lam ∉ S := fun h => hlam (Set.mem_union_left _ h)
  have hlam0 : lam ≠ 0 := fun h => hlam (Set.mem_union_right _ (by simp [h]))
  have h1 : finrank K (V ⧸ (Ideal.span {(X - C (1 : K) : K[X])} • (⊤ : Submodule K[X] V))) = r := by
    rw [← hconst lam hlam0]
    exact heq lam hlamS
  rw [h1]
  exact hge 0

end GaloisForLFunctions.HTGeometry
