import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# Moving the start of a short window by one

A mean-square theorem is stated for a continuous start `x`; the arithmetic construction uses the
integer start `⌊x⌋`.  The two differ by at most the two endpoint terms, because moving the start
from `t` to `t+1` drops exactly the term at `t+1` and adds exactly the term at `t+1+L`:

`∑_{t+1 < n ≤ t+1+L} f(n) - ∑_{t < n ≤ t+L} f(n) = f(t+1+L) - f(t+1)`.

The identity is exact and holds for every `L`, including `L = 0`.  For a bounded coefficient — the
Möbius function in particular — the two window sums therefore differ by at most two.
-/

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-- A one-step window `Ioc m (m+1)` is the singleton `{m+1}`. -/
theorem sum_Ioc_succ_self (f : ℕ → ℤ) (m : ℕ) :
    ∑ n ∈ Finset.Ioc m (m + 1), f n = f (m + 1) := by
  have hset : Finset.Ioc m (m + 1) = {m + 1} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  rw [hset, Finset.sum_singleton]

/-- **Shifting the start by one.**  Exactly one term leaves and one enters. -/
theorem sum_Ioc_succ_sub (f : ℕ → ℤ) (t L : ℕ) :
    (∑ n ∈ Finset.Ioc (t + 1) (t + 1 + L), f n) - (∑ n ∈ Finset.Ioc t (t + L), f n)
      = f (t + 1 + L) - f (t + 1) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · have h1 : (∑ n ∈ Finset.Ioc t (t + 1), f n) + (∑ n ∈ Finset.Ioc (t + 1) (t + L), f n)
        = ∑ n ∈ Finset.Ioc t (t + L), f n :=
      Finset.sum_Ioc_consecutive f (by omega) (by omega)
    have h2 : (∑ n ∈ Finset.Ioc (t + 1) (t + L), f n)
          + (∑ n ∈ Finset.Ioc (t + L) (t + 1 + L), f n)
        = ∑ n ∈ Finset.Ioc (t + 1) (t + 1 + L), f n :=
      Finset.sum_Ioc_consecutive f (by omega) (by omega)
    have h3 : ∑ n ∈ Finset.Ioc t (t + 1), f n = f (t + 1) := sum_Ioc_succ_self f t
    have h4 : ∑ n ∈ Finset.Ioc (t + L) (t + 1 + L), f n = f (t + 1 + L) := by
      have hrw : t + 1 + L = (t + L) + 1 := by omega
      rw [hrw]
      exact sum_Ioc_succ_self f (t + L)
    omega

/-- **Two endpoint terms.**  For a coefficient bounded by one the two window sums differ by at
most two. -/
theorem abs_sum_Ioc_succ_sub_le {f : ℕ → ℤ} (hf : ∀ n, |f n| ≤ 1) (t L : ℕ) :
    |(∑ n ∈ Finset.Ioc (t + 1) (t + 1 + L), f n) - (∑ n ∈ Finset.Ioc t (t + L), f n)| ≤ 2 := by
  rw [sum_Ioc_succ_sub f t L]
  have h1 := hf (t + 1 + L)
  have h2 := hf (t + 1)
  rw [abs_le] at h1 h2 ⊢
  omega

/-- The Möbius window sums at consecutive integer starts differ by at most two. -/
theorem abs_sum_Ioc_moebius_succ_sub_le (t L : ℕ) :
    |(∑ n ∈ Finset.Ioc (t + 1) (t + 1 + L), μ n) - (∑ n ∈ Finset.Ioc t (t + L), μ n)| ≤ 2 :=
  abs_sum_Ioc_succ_sub_le (fun _ => ArithmeticFunction.abs_moebius_le_one) t L

end RHTower.Sieve
