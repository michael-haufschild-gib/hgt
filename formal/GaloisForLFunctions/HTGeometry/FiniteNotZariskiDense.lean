import GaloisForLFunctions.HTGeometry.Sl2AdjointIrreducible
import Mathlib.Algebra.Polynomial.Roots

/-!
# A finite subgroup is not Zariski dense in `SL₂`

The upper unipotents form an injective line inside the determinant-one matrices, so their
`(0,1)` entries take every value of the field.  A finite set of matrices is therefore separated
from `SL₂` by a single-variable polynomial in that entry: the product of the linear factors at the
entries occurring in the set vanishes on the set, and — the field being infinite — misses some
unipotent.

This is the elementary half of "a Zariski-dense differential algebraic subgroup has a nonzero Lie
algebra": a group with no infinitesimal directions is finite, and a finite group is not dense.

* `unipotentUpper_injective`, `unipotentUpper_entry`;
* `exists_separating_poly_of_finite`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable {U : Type*} [Field U]

@[simp] theorem unipotentUpper_entry (t : U) : unipotentUpper t 0 1 = t := by
  rw [unipotentUpper]
  simp

theorem unipotentUpper_injective :
    Function.Injective (unipotentUpper : U → Matrix (Fin 2) (Fin 2) U) := by
  intro s t hst
  have := congrArg (fun M => M 0 1) hst
  simpa using this

/-- **A finite set of matrices is separated from `SL₂` by one polynomial in the `(0,1)` entry.** -/
theorem exists_separating_poly_of_finite [Infinite U]
    {G : Set (Matrix (Fin 2) (Fin 2) U)} (hfin : G.Finite) :
    ∃ q : Polynomial U, q ≠ 0 ∧ (∀ g ∈ G, q.eval (g 0 1) = 0) ∧
      ∃ g : Matrix (Fin 2) (Fin 2) U, g.det = 1 ∧ q.eval (g 0 1) ≠ 0 := by
  classical
  set s : Finset (Matrix (Fin 2) (Fin 2) U) := hfin.toFinset with hs
  set q : Polynomial U := ∏ h ∈ s, (X - C (h 0 1)) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]
    refine Finset.prod_ne_zero_iff.mpr fun h _ => ?_
    exact X_sub_C_ne_zero (h 0 1)
  have hvanish : ∀ g ∈ G, q.eval (g 0 1) = 0 := by
    intro g hg
    rw [hq, eval_prod]
    refine Finset.prod_eq_zero (i := g) ?_ ?_
    · rw [hs]
      simpa using hg
    · simp
  have hroots : (q.roots.toFinset : Set U).Finite := q.roots.toFinset.finite_toSet
  obtain ⟨t, ht⟩ := Set.Infinite.nonempty (Set.Infinite.sdiff (Set.infinite_univ (α := U)) hroots)
  have htne : q.eval t ≠ 0 := by
    intro h0
    have : t ∈ q.roots := (mem_roots hq0).mpr (by simpa [IsRoot] using h0)
    exact ht.2 (by simpa using this)
  have hdet : (unipotentUpper t).det = 1 := by
    rw [unipotentUpper, Matrix.det_fin_two_of]
    ring
  refine ⟨q, hq0, hvanish, unipotentUpper t, hdet, ?_⟩
  rwa [unipotentUpper_entry]

end

end GaloisForLFunctions.HTGeometry
