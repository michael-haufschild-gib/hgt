import GaloisForLFunctions.RHTower.Sieve.ParityReduction

/-!
# Swapping a doubly-constrained double sum

The weighted tail is summed first over the outer variable and then over a range depending on it.
Turning it into an `r`-sum — which is how the exponent budget adds up — is a filter swap.
-/

namespace RHTower.Sieve

open Finset

/-- **Swapping the order of a filtered double sum.** -/
theorem sum_filter_swap {α : Type*} [AddCommMonoid α] (S Tset : Finset ℕ)
    (P : ℕ → ℕ → Prop) [DecidableRel P] (F : ℕ → ℕ → α) :
    (∑ m ∈ S, ∑ r ∈ Tset.filter (P m), F m r)
      = ∑ r ∈ Tset, ∑ m ∈ S.filter (fun m => P m r), F m r := by
  classical
  have hleft : (∑ m ∈ S, ∑ r ∈ Tset.filter (P m), F m r)
      = ∑ m ∈ S, ∑ r ∈ Tset, if P m r then F m r else 0 :=
    Finset.sum_congr rfl fun m _ => Finset.sum_filter _ _
  have hright : (∑ r ∈ Tset, ∑ m ∈ S.filter (fun m => P m r), F m r)
      = ∑ r ∈ Tset, ∑ m ∈ S, if P m r then F m r else 0 :=
    Finset.sum_congr rfl fun r _ => Finset.sum_filter _ _
  rw [hleft, hright, Finset.sum_comm]

end RHTower.Sieve
