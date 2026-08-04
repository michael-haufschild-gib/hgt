import GaloisForLFunctions.HTGeometry.KummerDegreeBound
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The degree of a many-coordinate radical extension

Adjoining finitely many elements, each of which has a power in the base field, multiplies degrees:
the extension degree is at most the product of the exponents.  Each step of the tower is a radical
extension of degree at most its exponent, and the tower law multiplies them.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

noncomputable section

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The degree of a finitely generated radical extension.**  Adjoining a finite family of elements
whose powers lie in the base multiplies the exponents. -/
theorem finrank_adjoin_image_le_prod {ι : Type*} [DecidableEq ι] (x : ι → L) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) (hmem : ∀ i, ∃ c : F, x i ^ n i = algebraMap F L c) (s : Finset ι) :
    Module.finrank F ↥(IntermediateField.adjoin F (x '' (s : Set ι))) ≤ ∏ i ∈ s, n i := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hset : (x '' ((∅ : Finset ι) : Set ι)) = (∅ : Set L) := by simp
      rw [hset, IntermediateField.adjoin_empty, Finset.prod_empty,
        IntermediateField.finrank_bot]
  | insert a s ha ih =>
      have hstep : IntermediateField.adjoin F (x '' ((insert a s : Finset ι) : Set ι))
          = (IntermediateField.adjoin
              (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
              ({x a} : Set L)).restrictScalars F := by
        rw [IntermediateField.adjoin_adjoin_left]
        congr 1
        rw [Finset.coe_insert, Set.image_insert_eq, Set.union_singleton]
      have hcmem : x a ^ n a ∈ IntermediateField.adjoin F (x '' (s : Set ι)) := by
        obtain ⟨c, hc⟩ := hmem a
        rw [hc]
        exact IntermediateField.algebraMap_mem _ c
      have hlast : Module.finrank (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
          ↥(IntermediateField.adjoin (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
            ({x a} : Set L)) ≤ n a := by
        exact finrank_adjoin_le_of_pow_mem (α := x a)
          (c := (⟨x a ^ n a, hcmem⟩ :
            ↥(IntermediateField.adjoin F (x '' (s : Set ι))))) (hn a) rfl
      have htower := Module.finrank_mul_finrank F
        (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
        ↥(IntermediateField.adjoin (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
          ({x a} : Set L))
      rw [hstep, Finset.prod_insert ha]
      calc Module.finrank F ↥((IntermediateField.adjoin
            (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
            ({x a} : Set L)).restrictScalars F)
          = Module.finrank F (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
              * Module.finrank (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
                ↥(IntermediateField.adjoin (↥(IntermediateField.adjoin F (x '' (s : Set ι))))
                  ({x a} : Set L)) := htower.symm
        _ ≤ (∏ i ∈ s, n i) * n a := Nat.mul_le_mul ih hlast
        _ = n a * ∏ i ∈ s, n i := Nat.mul_comm _ _

end

end GaloisForLFunctions.HTGeometry
