import Mathlib

/-!
# Telescoping a sum over an interval into antitone blocks

An antitone sequence of endpoints `n : ℕ → ℕ` cuts the interval `Ioc (n K) (n 0)` into the `K`
consecutive blocks `Ioc (n (k+1)) (n k)` (`sum_Ioc_eq_sum_blocks`).  This is the combinatorial step
behind every dilation limit: the weight is constant on each block, so the sum telescopes into an
alternating difference of summatory values.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Block decomposition of a sum over an interval.** -/
theorem sum_Ioc_eq_sum_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ → ℕ)
    (hn : Antitone n) (K : ℕ) :
    ∑ m ∈ Finset.Ioc (n K) (n 0), f m
      = ∑ k ∈ Finset.range K, ∑ m ∈ Finset.Ioc (n (k + 1)) (n k), f m := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hle1 : n (K + 1) ≤ n K := hn (Nat.le_succ K)
      have hle2 : n K ≤ n 0 := hn (Nat.zero_le K)
      rw [Finset.sum_range_succ, ← ih,
        ← Finset.sum_Ioc_consecutive f hle1 hle2]
      exact add_comm _ _

end GaloisForLFunctions.HTGeometry
