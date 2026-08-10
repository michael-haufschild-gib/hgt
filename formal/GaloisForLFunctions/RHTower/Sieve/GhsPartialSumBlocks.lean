import GaloisForLFunctions.RHTower.Sieve.GhsOuterCovered

/-!
# The partial sum against the blocks

The top of the chain.  The logarithmic recursion turns `(∑_{n ≤ N} f)·log N` into the summatory
function of the triple convolution up to `O(N log log N)`; the blocks split that summatory function
into `K` pieces, each with its own inner cutoff.  Together:

```text
‖(∑_{n ≤ N} f)·log N‖ ≤ ghsRecursionError N + K·D ,
```

whenever each of the `K` blocks contributes at most `D`.  With the geometric scales `K ≍ log log N`
and, at the parameters of the argument, `D ≍ V·N` — so the bound is
`‖∑_{n≤N} f‖ ≲ N·(log log N/log N + V·log log N/log N)`, which for `V` the damped size
`≍ (log N)e^{−m}` is `N·e^{−m}·log log N`.

That is the ceiling the absolute-value route can reach, and it is within `log log N/(1+m)` of
Halász — the two agreeing at the extremal `m ≍ log log N`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The cost of the two applications of the logarithmic recursion. -/
def ghsRecursionError (N : ℕ) : ℝ :=
  (9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
    + (9 + RHTower.Mertens.mertensTail)
        * ((N : ℝ)
            * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                  / Real.log 2)
                * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ))))

/-- **The partial sum against the blocks.** -/
theorem norm_sum_Icc_mul_log_blocks_le
    {f : ℕ → ℂ} (hf : ∀ p q : ℕ, f (p * q) = f p * f q) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {N : ℕ} (hN : 2 ≤ N) {a : ℕ → ℕ} (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (ha0 : a 0 = 1)
    (K : ℕ) (haK : N / 2 ≤ a K) {D : ℝ}
    (hbd : ∀ k, k < K →
      ‖∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
          (LSeries.convolution (ghsInner f (N / a k)) f)) n‖ ≤ D) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ghsRecursionError N + (K : ℝ) * D := by
  have hrec := norm_sum_Icc_mul_log_sub_ghsTriple_le (f := f) hf hbdd N hN
  have hblocks := norm_sum_Icc_ghsOuter_blocks_le f f N ha haA ha0 K N haK le_rfl hbd
  have htri : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N,
                (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
        + ‖∑ n ∈ Finset.Icc 1 N,
            (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N,
            (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
      (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
    simpa using h
  rw [ghsRecursionError]
  linarith [htri, hrec, hblocks]

end RHTower.Sieve

end
