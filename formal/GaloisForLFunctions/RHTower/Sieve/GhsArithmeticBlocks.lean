import GaloisForLFunctions.RHTower.Sieve.GhsSumBlocksBound

/-!
# The blocks at the arithmetic level

The triple convolution of the argument is linear in its outer factor, so the geometric partition of
the outer prime range splits the summatory function itself:

```text
∑_{n ≤ M} (ghsOuterBlock f N (a 0) (a K) ⍟ h)(n)
  = ∑_{k < K} ∑_{n ≤ M} (ghsOuterBlock f N (a k) (a (k+1)) ⍟ h)(n) .
```

This is where the blocks enter — before Perron, not after.  It is what lets each block carry its
own inner truncation `N/A_k`, which the balance requires and which a single Perron integral with a
fixed inner factor cannot provide.

Nothing analytic: the convolution is a finite sum over the divisor antidiagonal, and the outer
weight's telescope moves through it by `Finset.sum_comm`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The convolution telescopes in its outer factor.** -/
theorem convolution_ghsOuterBlock_telescope (f h : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ} (ha : Monotone a)
    (K n : ℕ) :
    (LSeries.convolution (ghsOuterBlock f N (a 0) (a K)) h) n
      = ∑ k ∈ Finset.range K,
          (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1))) h) n := by
  classical
  simp only [LSeries.convolution_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ghsOuterBlock_telescope f N ha K p.1, Finset.sum_mul]

/-- **The summatory function of the triple convolution splits over the blocks.** -/
theorem sum_Icc_convolution_ghsOuterBlock_telescope (f h : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ}
    (ha : Monotone a) (K M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (LSeries.convolution (ghsOuterBlock f N (a 0) (a K)) h) n
      = ∑ k ∈ Finset.range K,
          ∑ n ∈ Finset.Icc 1 M,
            (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1))) h) n := by
  classical
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => convolution_ghsOuterBlock_telescope f h N ha K n

/-- **The inner truncation of a block is invisible.**  For an outer weight supported above `A`, a
term of the triple convolution at `n ≤ N` has its inner index below `N/A`, so truncating the inner
weight there changes nothing. -/
theorem convolution_ghsInner_trunc_eq {f : ℕ → ℂ} {N A B n : ℕ} (hA : 1 ≤ A) (hn : n ≤ N)
    (hnpos : 0 < n) (F : ℕ → ℂ) :
    (LSeries.convolution (ghsOuterBlock f N A B)
        (LSeries.convolution (ghsInner f N) F)) n
      = (LSeries.convolution (ghsOuterBlock f N A B)
        (LSeries.convolution (ghsInner f (N / A)) F)) n := by
  classical
  simp only [LSeries.convolution_def]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hpe, hne⟩ := hp
  by_cases hz : ghsOuterBlock f N A B p.1 = 0
  · rw [hz, zero_mul, zero_mul]
  · have hmem := ghsOuterBlock_supp hz
    have hpA : A < p.1 := by
      rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hmem
      by_contra hc
      exact hmem.2 ⟨by omega, hmem.1.2⟩
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hq
    obtain ⟨hqe, -⟩ := hq
    have hq1 : q.1 * p.1 ≤ N := by
      have : p.1 * (q.1 * q.2) = n := by rw [hqe, hpe]
      calc q.1 * p.1 ≤ p.1 * (q.1 * q.2) := by
            rcases Nat.eq_zero_or_pos q.2 with h0 | h0
            · exfalso
              rw [h0, Nat.mul_zero] at hqe
              rw [← hqe, Nat.mul_zero] at hpe
              omega
            · nlinarith [h0]
        _ = n := this
        _ ≤ N := hn
    have hqle : q.1 ≤ N / A := by
      have hpAle : A ≤ p.1 := by omega
      have h1 : q.1 * A ≤ N := le_trans (Nat.mul_le_mul_left q.1 hpAle) hq1
      exact (Nat.le_div_iff_mul_le (by omega)).2 h1
    congr 1
    rw [ghsInner, ghsInner]
    by_cases hqp : Nat.Prime q.1
    · rw [if_pos ⟨hqp, le_trans hqle (Nat.div_le_self N A)⟩, if_pos ⟨hqp, hqle⟩]
    · rw [if_neg (by tauto), if_neg (by tauto)]

end RHTower.Sieve

end
