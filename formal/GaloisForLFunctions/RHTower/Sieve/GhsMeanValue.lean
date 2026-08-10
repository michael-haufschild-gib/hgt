import GaloisForLFunctions.RHTower.Sieve.GhsBlockD

/-!
# The mean value, in Halász's shape

Dividing the capstone by `log N` puts the argument in the form a mean-value theorem is stated in:

```text
‖∑_{n ≤ N} f(n)‖ ≤ ( ghsRecursionError N + K·(E + (1/2π)·V·(N+½)^σ·C) ) / log N .
```

The first term is `O(N·log log N/log N)`, the second `O(K·V·N/log N)`.  With `K ≍ log log N` from
the geometric scales and `V` the damped size `≍ (log N)·e^{−m}`, the whole is
`N·(log log N/log N + e^{−m}·log log N)`.

That is the endpoint of the Granville–Harper–Soundararajan chain in this corpus: non-trivial as
soon as `m ≥ log log log N + ω(1)`, against `m ≥ log log N` before this thread, and within
`log log N/(1 + m)` of Halász's `(1 + m)e^{−m}` — the two agreeing at the extremal
`m ≍ log log N`, which is where the absolute-value route is provably optimal.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

/-- **The capstone with `D` written out.** -/
theorem norm_sum_Icc_mul_log_ghs_explicit
    {f : ℕ → ℂ} (hf : ∀ p q : ℕ, f (p * q) = f p * f q) (hbdd : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N : ℕ} (hN : 2 ≤ N) {a : ℕ → ℕ} (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (ha0 : a 0 = 1)
    (K : ℕ) (haK : N / 2 ≤ a K) {σ E V C : ℝ}
    (hblock : ∀ k, k < K →
      ‖∑ i ∈ Finset.Icc 1 N,
          (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
            (LSeries.convolution (ghsInner f (N / a k)) f)) i‖
        ≤ E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C)) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ghsRecursionError N
          + (K : ℝ) * (E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C)) :=
  norm_sum_Icc_mul_log_blocks_le hf hbdd hN ha haA ha0 K haK hblock

/-- **The mean value.**  The capstone divided by `log N`. -/
theorem norm_sum_Icc_le_ghs
    {f : ℕ → ℂ} (hf : ∀ p q : ℕ, f (p * q) = f p * f q) (hbdd : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N : ℕ} (hN : 2 ≤ N) {a : ℕ → ℕ} (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (ha0 : a 0 = 1)
    (K : ℕ) (haK : N / 2 ≤ a K) {σ E V C : ℝ}
    (hblock : ∀ k, k < K →
      ‖∑ i ∈ Finset.Icc 1 N,
          (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
            (LSeries.convolution (ghsInner f (N / a k)) f)) i‖
        ≤ E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C)) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖
      ≤ (ghsRecursionError N
            + (K : ℝ) * (E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C)))
          / Real.log (N : ℝ) := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hbase := norm_sum_Icc_mul_log_ghs_explicit hf hbdd hN ha haA ha0 K haK hblock
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  rw [hnorm] at hbase
  rw [le_div_iff₀ hlog]
  exact hbase

end RHTower.Sieve

end
