import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Telescoping partition of an interval sum

An antitone sequence of cut points `d 0 ≥ d 1 ≥ ⋯ ≥ d K` tiles the
interval `(d K, d 0]` by the blocks `(d (k+1), d k]`, so any sum over the
interval splits into the block sums.
-/

namespace HTGeometry

open Finset

/-- **Ioc partition sum**: block sums over antitone cuts telescope. -/
theorem sum_Ioc_partition {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (d : ℕ → ℕ) (K : ℕ) (hanti : ∀ k, k < K → d (k + 1) ≤ d k) :
    ∑ k ∈ Finset.range K, ∑ m ∈ Finset.Ioc (d (k + 1)) (d k), f m
      = ∑ m ∈ Finset.Ioc (d K) (d 0), f m := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hchain : d K ≤ d 0 := by
      have haux : ∀ j, j ≤ K → d j ≤ d 0 := by
        intro j
        induction j with
        | zero => intro _; exact le_rfl
        | succ i ihi =>
          intro hij
          exact le_trans (hanti i (by omega)) (ihi (by omega))
      exact haux K le_rfl
    rw [Finset.sum_range_succ, ih (fun k hk => hanti k (by omega)),
      add_comm]
    have hdisj : Disjoint (Finset.Ioc (d (K + 1)) (d K))
        (Finset.Ioc (d K) (d 0)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Ioc] at hx hx'
      omega
    rw [← Finset.sum_union hdisj,
      Finset.Ioc_union_Ioc_eq_Ioc (hanti K (by omega)) hchain]

end HTGeometry
