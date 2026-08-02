import GaloisForLFunctions.HTGeometry.RootSubsetInvariantSubspace

/-!
# Shift-invariant subspaces of the given dimension are exactly the root subsets

The two directions, in one statement: a subspace of `K[t]/(1 + t^L)` is invariant under
multiplication by `t` and of dimension `m` exactly when it is the ideal cut out by an `n`-element set
of roots.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The `m`-dimensional shift-invariant subspaces are the `n`-element root subsets.** -/
theorem invariantSubspace_iff_rootSubset {m n : ℕ} (hL : 0 < m + n)
    (V : Submodule K (K[X] ⧸ Ideal.span
      ({pureCriticalCyclicPolynomial (K := K) (m + n)} : Set K[X]))) :
    ((∀ v ∈ V, (Ideal.Quotient.mk
        (Ideal.span ({pureCriticalCyclicPolynomial (K := K) (m + n)} : Set K[X])) X) * v ∈ V)
      ∧ Module.finrank K V = m)
      ↔ ∃ S : Finset (Fin (m + n)), S.card = n ∧
          ∀ v, v ∈ V ↔ v ∈ Ideal.map (Ideal.Quotient.mkₐ K (Ideal.span
              ({pureCriticalCyclicPolynomial (K := K) (m + n)} : Set K[X])))
            (Ideal.span ({∏ i ∈ S, (X - C (pureCriticalRootLabeling (K := K) hL i))} :
              Set K[X])) := by
  constructor
  · rintro ⟨hinv, hdim⟩
    obtain ⟨S, hScard, hSmem⟩ := exists_rootSubset_of_invariantSubspace hL V hinv hdim
    refine ⟨S, hScard, fun v => ?_⟩
    rw [hSmem v, Ideal.map_span]
    congr! 2
    simp
  · rintro ⟨S, hScard, hSmem⟩
    have hVeq : Submodule.restrictScalars K
        (Ideal.map (Ideal.Quotient.mkₐ K (Ideal.span
            ({pureCriticalCyclicPolynomial (K := K) (m + n)} : Set K[X])))
          (Ideal.span ({∏ i ∈ S, (X - C (pureCriticalRootLabeling (K := K) hL i))} :
            Set K[X]))) = V :=
      SetLike.ext (fun v => (hSmem v).symm)
    constructor
    · intro v hv
      rw [hSmem] at hv ⊢
      exact Ideal.mul_mem_left _ _ hv
    · rw [← hVeq, finrank_ideal_rootSubset hL S hScard]

end GaloisForLFunctions.HTGeometry
