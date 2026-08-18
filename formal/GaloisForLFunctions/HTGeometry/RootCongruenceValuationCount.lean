import Mathlib

/-!
# Congruent roots are counted by the derivative

Let `W` be a discrete valuation ring and `f` a monic polynomial over `W` that splits.  For a root
`x` of `f`,

```text
f'(x) = ∏_{a ∈ roots.erase x} (x - a)                    Splits.eval_root_derivative
```

so a single root `y ≠ x` congruent to `x` modulo the maximal ideal already forces `f'(x)` to be a
non-unit.  Combined with the elementary bound "the number of members of a set on which a function
is nonzero is at most the total sum", this turns a bound on `∑_x v(f'(x))` into a bound on the
number of roots that collide after reduction:

```text
addVal_multiset_prod                              v(∏ s) = ∑ v
addVal_multiset_prod_ne_zero_of_mem               one non-unit factor spoils the product
addVal_eval_derivative_ne_zero_of_root_congruent
    ** x ≡ y (mod 𝔪), x ≠ y roots  ⟹  v(f'(x)) ≠ 0 **
ncard_le_of_sum_addVal_le                         #{a ∈ S} ≤ ∑ g  when g ≠ 0 on S
```

No hypothesis on the residue field, and no separability: the count is pure valuation theory.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

/-- The additive valuation of a multiset product is the sum of the valuations. -/
theorem addVal_multiset_prod (s : Multiset W) :
    addVal W s.prod = (s.map (addVal W)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [Multiset.prod_cons, ih]

/-- A single non-unit factor makes the whole product a non-unit. -/
theorem addVal_multiset_prod_ne_zero_of_mem {s : Multiset W} {b : W} (hb : b ∈ s)
    (h : addVal W b ≠ 0) : addVal W s.prod ≠ 0 := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hb
  rw [Multiset.prod_cons, addVal_mul]
  simp only [ne_eq, add_eq_zero, not_and]
  exact fun h1 => absurd h1 h

/-- **A congruent pair of roots is seen by the derivative.**  If two distinct roots of a monic split
polynomial are congruent modulo the maximal ideal, the derivative is a non-unit at either of
them. -/
theorem addVal_eval_derivative_ne_zero_of_root_congruent
    {f : W[X]} (hf : f.Splits) (hm : f.Monic) {x y : W}
    (hx : x ∈ f.roots) (hy : y ∈ f.roots) (hxy : x ≠ y)
    (h : addVal W (x - y) ≠ 0) :
    addVal W (f.derivative.eval x) ≠ 0 := by
  classical
  rw [hf.eval_root_derivative hm hx]
  refine addVal_multiset_prod_ne_zero_of_mem (b := x - y) ?_ h
  exact Multiset.mem_map_of_mem _ ((Multiset.mem_erase_of_ne (Ne.symm hxy)).mpr hy)

/-- **Counting by a valuation.**  A set on which a `ℕ∞`-valued function is everywhere nonzero has
at most as many elements as the total sum of that function. -/
theorem ncard_le_of_sum_addVal_le {α : Type*} [Fintype α] {S : Set α} {g : α → ℕ∞} {N : ℕ}
    (hS : ∀ a ∈ S, g a ≠ 0) (h : ∑ a, g a ≤ (N : ℕ∞)) : S.ncard ≤ N := by
  classical
  have hcast : (S.ncard : ℕ∞) ≤ (N : ℕ∞) := by
    have h1 : (S.ncard : ℕ∞) = ∑ _a ∈ S.toFinset, (1 : ℕ∞) := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    rw [h1]
    refine le_trans (Finset.sum_le_sum ?_) (le_trans (Finset.sum_le_sum_of_subset
      (Finset.subset_univ S.toFinset)) h)
    intro a ha
    exact Order.one_le_iff_ne_zero.mpr (hS a (Set.mem_toFinset.mp ha))
  exact_mod_cast hcast

end GaloisForLFunctions.HTGeometry
