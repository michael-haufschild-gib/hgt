import GaloisForLFunctions.RHTower.Sieve.GhsBlocksTotal

/-!
# The blocks cover the outer weight

The outer weight `ghsOuter f N` is supported on primes `p` with `2 ≤ N/p`, hence on `p ≤ N/2`.  So
a family of blocks starting at `1` and reaching `N/2` covers it exactly:

```text
ghsOuterBlock f N 1 C = ghsOuter f N        whenever  N/2 ≤ C .
```

With that, the telescope applies to the object the logarithmic recursion actually produces, and the
whole chain closes:

```text
‖∑_{n ≤ M} (ghsOuter f N ⍟ (ghsInner f N ⍟ F))(n)‖ ≤ K·D
```

as soon as each of the `K` blocks contributes at most `D`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **A block from `1` to anything past `N/2` is the whole outer weight.** -/
theorem ghsOuterBlock_eq_ghsOuter {f : ℕ → ℂ} {N C : ℕ} (hC : N / 2 ≤ C) (p : ℕ) :
    ghsOuterBlock f N 1 C p = ghsOuter f N p := by
  classical
  by_cases hmem : p ∈ Nat.primesLE C \ Nat.primesLE 1
  · exact ghsOuterBlock_eq hmem
  · rw [ghsOuterBlock, if_neg hmem]
    by_cases hp : Nat.Prime p
    · have hp2 : 2 ≤ p := hp.two_le
      have hnot : ¬ (p ≤ C) := by
        intro hpC
        exact hmem (by
          rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
          exact ⟨⟨hpC, hp⟩, by intro hc; omega⟩)
      have hpN : N < 2 * p := by
        have h1 : C < p := by omega
        have h2 : N / 2 < p := by omega
        omega
      have hdiv : N / p < 2 := by
        by_contra hc
        have : 2 * p ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 (by omega)
        omega
      rw [ghsOuter, if_neg (by intro hcc; omega)]
    · rw [ghsOuter, if_neg (by tauto)]

/-- **The whole outer range, split into blocks.** -/
theorem norm_sum_Icc_ghsOuter_blocks_le (f F : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ}
    (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (ha0 : a 0 = 1) (K M : ℕ) (haK : N / 2 ≤ a K)
    (hMN : M ≤ N) {D : ℝ}
    (hbd : ∀ k, k < K →
      ‖∑ n ∈ Finset.Icc 1 M,
        (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
          (LSeries.convolution (ghsInner f (N / a k)) F)) n‖ ≤ D) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) F)) n‖
      ≤ (K : ℝ) * D := by
  have hfun : ghsOuter f N = ghsOuterBlock f N (a 0) (a K) := by
    funext p
    rw [ha0, ghsOuterBlock_eq_ghsOuter haK p]
  rw [hfun]
  exact norm_sum_Icc_ghsOuterBlock_blocks_le f F N ha haA K M hMN hbd

end RHTower.Sieve

end
