import GaloisForLFunctions.HTGeometry.FibreNoTorsion

/-!
# A point without torsion has the smallest fibre

```text
finrank_fibre_le_of_smul_injective  ** a point where the parameter acts injectively has fibre
                                       dimension at most that of any other point **
```

This is the one-sided form of `finrank_fibre_eq_of_smul_injective`: torsion-freeness is needed only
at the *generic* point, and the special point — where the family is typically not torsion-free —
enters only through the free rank, which is a lower bound for every fibre.

That asymmetry is what a degeneration argument actually consumes.  The special fibre of a Gröbner
degeneration is the initial ideal, which is exactly where the family may fail to be flat in the naive
sense; the nonzero fibres are all isomorphic and torsion-free, so the inequality runs from the
generic fibre to the special one, which is the direction the Hilbert-function bookkeeping needs.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

/-- **A point with no torsion has fibre dimension at most that of any other point.** -/
theorem finrank_fibre_le_of_smul_injective {V : Type*} [AddCommGroup V] [Module K[X] V]
    [Module K V] [IsScalarTower K K[X] V] [Module.Finite K[X] V] {lam : K}
    (hlam : ∀ v : V, (X - C lam : K[X]) • v = 0 → v = 0) (mu : K) :
    finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))
      ≤ finrank K (V ⧸ (Ideal.span {(X - C mu : K[X])} • (⊤ : Submodule K[X] V))) := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨eqv0⟩⟩ := Module.equiv_free_prod_directSum K[X] V
  haveI := hι
  haveI : DecidableEq ι := Classical.decEq ι
  have eqv : V ≃ₗ[K[X]] (Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})) :=
    eqv0.trans ((LinearEquiv.refl K[X] (Fin n →₀ K[X])).prodCongr
      (DirectSum.linearEquivFunOnFintype K[X] ι (fun i => K[X] ⧸ (Ideal.span {p i ^ e i}))))
  have hpne : ∀ i, p i ≠ 0 := fun i => (hp i).ne_zero
  have hzero : (∑ i, (if (X - C lam : K[X]) ∣ p i ^ e i then 1 else 0)) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg (not_dvd_of_smul_injective eqv hlam hpne i)
  rw [finrank_fibre_eq eqv lam, finrank_fibre_eq eqv mu, hzero, add_zero]
  omega

end GaloisForLFunctions.HTGeometry
