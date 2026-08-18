import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Congruent roots are counted by the derivative

Let `W` be a discrete valuation ring and `f` a monic polynomial over `W` that splits.  For a root
`x` of `f`,

```text
f'(x) = ∏_{a ∈ roots.erase x} (x - a)                    Splits.eval_root_derivative
```

so each root congruent to `x` modulo the maximal ideal contributes at least one to the valuation of
`f'(x)`.  Counting the non-unit factors of a product therefore bounds the number of roots colliding
with `x` after reduction:

```text
addVal_multiset_prod                              v(∏ s) = ∑ v
addVal_multiset_prod_ne_zero_of_mem               one non-unit factor spoils the product
card_filter_addVal_ne_zero_le                     #{non-unit factors} ≤ v(∏ s)
addVal_eval_derivative_ne_zero_of_root_congruent
    x ≡ y (mod 𝔪), x ≠ y roots  ⟹  v(f'(x)) ≠ 0
card_congruent_roots_le_addVal_eval_derivative
    ** #{roots congruent to x} ≤ v(f'(x)) **
ncard_le_of_sum_addVal_le                         #{a ∈ S} ≤ ∑ g when g ≠ 0 on S
```

No hypothesis on the residue field, and no separability: the count is pure valuation theory.  The
sharp form is the last-but-one statement — it says a collision class of size `k` forces the
derivative to vanish to order at least `k - 1`, which is what turns "the Jacobian has divisorial
order one" into "at most two sheets collide".
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem addVal_multiset_prod (s : Multiset W) :
    addVal W s.prod = (s.map (addVal W)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [Multiset.prod_cons, ih]

theorem addVal_multiset_prod_ne_zero_of_mem {s : Multiset W} {b : W} (hb : b ∈ s)
    (h : addVal W b ≠ 0) : addVal W s.prod ≠ 0 := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hb
  rw [Multiset.prod_cons, addVal_mul]
  simp only [ne_eq, add_eq_zero, not_and]
  exact fun h1 => absurd h1 h

/-- **The non-units among the factors are counted by the valuation of the product.** -/
theorem card_filter_addVal_ne_zero_le [DecidablePred fun a : W => addVal W a ≠ 0]
    (s : Multiset W) :
    (((s.filter fun a : W => addVal W a ≠ 0).card : ℕ) : ℕ∞) ≤ addVal W s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, addVal_mul]
      by_cases h : addVal W a ≠ 0
      · have hf : Multiset.filter (fun b : W => addVal W b ≠ 0) (a ::ₘ s)
            = a ::ₘ Multiset.filter (fun b : W => addVal W b ≠ 0) s :=
          Multiset.filter_cons_of_pos _ h
        rw [hf, Multiset.card_cons]
        push_cast
        rw [add_comm (addVal W a)]
        exact add_le_add ih (Order.one_le_iff_ne_zero.mpr h)
      · have hf : Multiset.filter (fun b : W => addVal W b ≠ 0) (a ::ₘ s)
            = Multiset.filter (fun b : W => addVal W b ≠ 0) s :=
          Multiset.filter_cons_of_neg _ h
        rw [hf]
        exact ih.trans le_add_self

theorem addVal_eval_derivative_ne_zero_of_root_congruent
    {f : W[X]} (hf : f.Splits) (hm : f.Monic) {x y : W}
    (hx : x ∈ f.roots) (hy : y ∈ f.roots) (hxy : x ≠ y)
    (h : addVal W (x - y) ≠ 0) :
    addVal W (f.derivative.eval x) ≠ 0 := by
  classical
  rw [hf.eval_root_derivative hm hx]
  refine addVal_multiset_prod_ne_zero_of_mem (b := x - y) ?_ h
  exact Multiset.mem_map_of_mem _ ((Multiset.mem_erase_of_ne (Ne.symm hxy)).mpr hy)

/-- **Congruent roots are counted by the derivative.**  The number of other roots congruent to `x`
is at most the valuation of the derivative at `x`. -/
theorem card_congruent_roots_le_addVal_eval_derivative
    {f : W[X]} (hf : f.Splits) (hm : f.Monic) {x : W} (hx : x ∈ f.roots) :
    letI := Classical.decEq W
    ((((f.roots.erase x).filter fun a : W => addVal W (x - a) ≠ 0).card : ℕ) : ℕ∞)
      ≤ addVal W (f.derivative.eval x) := by
  classical
  rw [hf.eval_root_derivative hm hx]
  have h := card_filter_addVal_ne_zero_le ((f.roots.erase x).map fun a => x - a)
  refine le_trans (le_of_eq ?_) h
  congr 1
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

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
