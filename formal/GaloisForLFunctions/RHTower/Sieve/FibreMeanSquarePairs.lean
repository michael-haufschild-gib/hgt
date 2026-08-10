import GaloisForLFunctions.RHTower.Sieve.SeparatedCount

/-!
# The fibre mean square as a bilinear form in the outer variable

The mean square that `MaximalWindowMeanSquare` bounds can be expanded directly in the *outer*
variable, with no passage to an integral at all:

```text
∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} f(b))²
  = ∑_{m, n} f(m)·f(n)·#{ a ∈ outerBlock : m, n ∈ innerFibre a } .
```

The kernel is the number of outer indices whose fibre contains both `m` and `n`; since
`b ∈ innerFibre x h a ↔ x ≤ ab ≤ x + h√x`, that is the number of `a` in the intersection of two
intervals, hence explicitly computable — the exact analogue of `overlap_card_eq`, in the variable
the mean square actually runs over.

This is a better route than sampling a step function at the points `log(x/a)`: it is an identity,
the signs are kept, and the discrete-to-continuous passage — the delicate step of Gallagher's proof
— is never needed.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The fibre sits inside the ambient range. -/
theorem innerFibre_subset_range (x h : ℝ) (a : ℕ) :
    innerFibre x h a ⊆ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊ := by
  rw [innerFibre]
  exact Finset.filter_subset _ _

/-- **The fibre mean square, expanded into pairs.** -/
theorem sum_fibreSq_eq_count (f : ℕ → ℝ) (x h : ℝ) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      = ∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
          ∑ n ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
            f m * f n
              * (((outerBlock x h).filter
                  (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ) := by
  classical
  set T := Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊ with hTdef
  -- expand each square and widen the ranges
  have hexp : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, f b) ^ 2
        = ∑ m ∈ T, ∑ n ∈ T,
            (if m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a then f m * f n else 0) := by
    intro a _
    rw [sq, Finset.sum_mul_sum]
    have hsub : innerFibre x h a ⊆ T := innerFibre_subset_range x h a
    rw [← Finset.sum_subset hsub (fun m _ hm => ?_)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [← Finset.sum_subset hsub (fun n _ hn => ?_)]
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [if_pos ⟨hm, hn⟩]
      · rw [if_neg (fun hc => hn hc.2)]
    · refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg (fun hc => hm hc.1)]
  rw [Finset.sum_congr rfl hexp]
  -- swap the outer index to the inside
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

end RHTower.Sieve

end
