import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Mertens' first theorem on a block of primes

Subtracting two instances of Mertens' first theorem in prime form evaluates the prime-weighted harmonic
sum over an interval:

`|∑_{y < p ≤ z} (log p)/p − (log z − log y)| ≤ 2C`,   `C = (log 4 + 4) + (8 + mertensTail)`.

The block form is what a dyadic decomposition of the prime range consumes: on a block
`(x^{1−e^{1−k}}, x^{1−e^{−k}}]` the sum is `(e − 1)e^{−k} log x + O(1)`, so a partition of the primes
into such blocks carries geometrically decreasing mass, and the number of blocks that matter is the
logarithm of the total — the mechanism behind the `1 + M` prefactor of Halász's theorem.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The primes up to `z` split at `y`. -/
theorem sum_prime_log_div_Icc_split {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    (∑ p ∈ Finset.Icc 1 z with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ))
      = (∑ p ∈ Finset.Icc 1 y with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ))
        + ∑ p ∈ Finset.Ioc y z with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ) := by
  classical
  have hsplit : Finset.Icc 1 z = Finset.Icc 1 y ∪ Finset.Ioc y z := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 y) (Finset.Ioc y z) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_Ioc] at hb
    omega
  rw [hsplit, Finset.filter_union, Finset.sum_union (hdisj.mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- **Mertens' first theorem on a block.** -/
theorem abs_sum_Ioc_prime_log_div_sub_le {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    |(∑ p ∈ Finset.Ioc y z with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ))
        - (Real.log (z : ℝ) - Real.log (y : ℝ))|
      ≤ 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) := by
  have hz : 1 ≤ z := le_trans hy hyz
  have hmz := RHTower.Mertens.mertens_first_prime z hz
  have hmy := RHTower.Mertens.mertens_first_prime y hy
  have hsplit := sum_prime_log_div_Icc_split hy hyz
  rw [abs_le] at hmz hmy ⊢
  constructor
  · linarith [hmz.1, hmy.2, hsplit]
  · linarith [hmz.2, hmy.1, hsplit]

/-- The one-sided block bound. -/
theorem sum_Ioc_prime_log_div_le {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    (∑ p ∈ Finset.Ioc y z with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ))
      ≤ (Real.log (z : ℝ) - Real.log (y : ℝ))
        + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) := by
  have h := abs_sum_Ioc_prime_log_div_sub_le hy hyz
  rw [abs_le] at h
  linarith [h.2]

end RHTower.Sieve

end
