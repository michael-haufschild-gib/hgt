import GaloisForLFunctions.HTGeometry.FibreFiniteDimensional

/-!
# Semicontinuity of the fibre dimension over the base line

```text
finrank_fibre_eq            the fibre of a decomposed module is the rank plus the torsion summands
                            whose annihilator vanishes at the point
exists_generic_fibre_rank   ** every fibre has dimension at least the rank, and all but finitely
                               many have dimension exactly the rank **
```

The computation reads the decomposition of `Module.equiv_free_prod_directSum` through the fibre
calculus: transport to the decomposed module, split the product, count the free part by its rank and
each cyclic part by whether its annihilator vanishes.  The exceptional set is then the roots of the
finitely many annihilators.

This is the semicontinuity a degeneration argument consumes.  Combined with the fact that all
nonzero fibres of a weight degeneration are isomorphic (`eval_homogenize`), it says the dimension at
`t = 1` is the rank, hence at most the dimension at `t = 0` — the inequality that turns equal
Hilbert functions on the two fibres into a regular sequence upstairs.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

open scoped Classical in
/-- **The fibre dimension of a decomposed module.** -/
theorem finrank_fibre_eq {V : Type*} [AddCommGroup V] [Module K[X] V] [Module K V]
    [IsScalarTower K K[X] V] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → K[X]}
    {e : ι → ℕ}
    (eqv : V ≃ₗ[K[X]] (Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})))
    (lam : K) :
    finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))
      = n + ∑ i, (if (X - C lam : K[X]) ∣ p i ^ e i then 1 else 0) := by
  haveI hpi : FiniteDimensional K ((∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})) ⧸
      (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X]
        (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i}))))) :=
    Module.Finite.equiv
      ((piQuotSmulEquiv (M := fun i => K[X] ⧸ (Ideal.span {p i ^ e i}))
        (Ideal.span {(X - C lam : K[X])})).restrictScalars K).symm
  have h1 : finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))
      = finrank K
        (((Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i}))) ⧸
          (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X]
            ((Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})))))) :=
    finrank_quot_congr _ eqv
  rw [h1, finrank_quot_prod, finrank_quotient_finsupp, finrank_quot_pi]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact finrank_quot_cyclic (p i ^ e i) lam

open scoped Classical in
/-- **Semicontinuity of the fibre dimension.**  Every fibre has dimension at least the rank, and all
but finitely many have dimension exactly the rank. -/
theorem exists_generic_fibre_rank {V : Type*} [AddCommGroup V] [Module K[X] V] [Module K V]
    [IsScalarTower K K[X] V] [Module.Finite K[X] V] :
    ∃ (r : ℕ) (S : Finset K),
      (∀ lam : K,
        r ≤ finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))) ∧
      (∀ lam : K, lam ∉ S →
        finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V))) = r) := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨eqv0⟩⟩ := Module.equiv_free_prod_directSum K[X] V
  haveI := hι
  haveI : DecidableEq ι := Classical.decEq ι
  have eqv : V ≃ₗ[K[X]] (Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})) :=
    eqv0.trans ((LinearEquiv.refl K[X] (Fin n →₀ K[X])).prodCongr
      (DirectSum.linearEquivFunOnFintype K[X] ι (fun i => K[X] ⧸ (Ideal.span {p i ^ e i}))))
  have hform := fun lam => finrank_fibre_eq eqv lam
  refine ⟨n, Finset.univ.biUnion (fun i => (p i ^ e i).roots.toFinset), ?_, ?_⟩
  · intro lam
    rw [hform lam]
    omega
  · intro lam hlam
    rw [hform lam, show (∑ i, (if (X - C lam : K[X]) ∣ p i ^ e i then 1 else 0)) = 0 from ?_,
      add_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hdvd
    refine hlam (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
    have hne : (p i ^ e i) ≠ 0 := pow_ne_zero _ (hp i).ne_zero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact Polynomial.dvd_iff_isRoot.mp hdvd

end GaloisForLFunctions.HTGeometry
