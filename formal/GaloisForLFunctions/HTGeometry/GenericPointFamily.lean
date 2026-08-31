import GaloisForLFunctions.HTGeometry.GenericFibreBound

/-!
# One generic point for finitely many modules

```text
exists_nonzero_notMem_biUnion  a nonzero point outside finitely many finite sets
exists_generic_point_forall    ** a single nonzero point at which every fibre in a finite family is
                                  no bigger than its fibre at zero **
```

Each module contributes a finite exceptional set; over an infinite field their union, together with
the origin, still misses a point.

This is what lets a degeneration argument deform a whole regular sequence at once: the `n` stages of
the sequence give `n` exceptional sets, and one generic point of the base line works for all of them
simultaneously, so the rescaled forms are regular at every stage.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

theorem exists_nonzero_notMem_biUnion [Infinite K] {n : ℕ} (S : Fin n → Finset K) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ i, lam ∉ S i := by
  classical
  have hfin : (((Finset.univ.biUnion S) : Finset K) : Set K) ∪ {(0 : K)} |>.Finite :=
    (Finset.univ.biUnion S).finite_toSet.union (Set.finite_singleton (0 : K))
  obtain ⟨lam, hlam⟩ := hfin.infinite_compl.nonempty
  refine ⟨lam, ?_, ?_⟩
  · intro h
    exact hlam (Set.mem_union_right _ (by simp [h]))
  · intro i hi
    refine hlam (Set.mem_union_left _ ?_)
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, by simp, hi⟩

/-- **One generic point serves finitely many modules at once**: there is a nonzero point of the base
line at which every fibre in a finite family has at most the dimension of its fibre at zero. -/
theorem exists_generic_point_forall [Infinite K] {n : ℕ} (V : Fin n → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K[X] (V i)] [∀ i, Module K (V i)]
    [∀ i, IsScalarTower K K[X] (V i)] [∀ i, Module.Finite K[X] (V i)] :
    ∃ lam : K, lam ≠ 0 ∧ ∀ i,
      finrank K ((V i) ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (V i))))
        ≤ finrank K ((V i) ⧸
          (Ideal.span {(X - C (0 : K) : K[X])} • (⊤ : Submodule K[X] (V i)))) := by
  classical
  choose r S hge heq using fun i => exists_generic_fibre_rank (K := K) (V := V i)
  obtain ⟨lam, hlam0, hlamS⟩ := exists_nonzero_notMem_biUnion S
  refine ⟨lam, hlam0, fun i => ?_⟩
  rw [heq i lam (hlamS i)]
  exact hge i 0

end GaloisForLFunctions.HTGeometry
