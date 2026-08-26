import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite sums under additive characters

Dependency-light finite-product transport for additive characters.  An additive character sends a
finite sum in its source to the corresponding finite product in its multiplicative target.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- An additive character maps a finite sum to the product of its character values. -/
theorem addChar_map_finsetSum {A R : Type*} [AddCommGroup A] [CommMonoid R]
    (ψ : AddChar A R) {κ : Type*} (s : Finset κ) (f : κ → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

end GaloisForLFunctions.HTGeometry
