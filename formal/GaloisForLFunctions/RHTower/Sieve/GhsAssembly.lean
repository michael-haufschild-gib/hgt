import GaloisForLFunctions.RHTower.Sieve.GhsUniformError

/-!
# The Granville–Harper–Soundararajan mean value over the trimmed partition

Every block of `ghsPart N n` has a bound of the same shape, so the capstone applies to the
partition as a whole:

* `k = 0` is `(1, n²]`, bounded trivially by `norm_sum_Icc_ghs_small_block_le`;
* `k = 1` is `(n², ghsBlockRight N 0]`, the trimmed block, by `ghs_block_D_trimmed_explicit`;
* `k ≥ 2` is the geometric block of index `k − 1`, by `ghs_block_D_geometric_explicit`.

The truncation errors are all at most `ghsUniformError N n σ`, and the trivial block's bound is
absorbed into the same `E`.  What comes out is

```text
‖∑_{m ≤ N} f(m)‖
  ≤ ( ghsRecursionError N
        + (K+1)·(E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
      / log N ,
```

with no hypothesis left about any individual block.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The mean value over the trimmed partition.** -/
theorem norm_sum_Icc_le_ghs_partition
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N n z K : ℕ} {σ δ E : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 2 ≤ N)
    (hPN : n ^ 2 ≤ N) (hNP : 2 ≤ N / n ^ 2)
    (hA0 : n ^ 2 ≤ ghsBlockRight N 0)
    (hthr : ∀ k, k < K → (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hBN : ∀ k, k < K → 2 ≤ N / ghsBlockRight N k)
    (hAk : ∀ k, 1 ≤ k → k < K → n ^ 2 ≤ ghsBlockLeft N k)
    (hheight : ∀ k, k < K →
      (5 / (4 * (n : ℝ))) * ((16 / 9) * 4 ^ (k + 1) * (Real.log N + Real.log 4))
        ≤ 1750 * ghsShapeConst)
    (hcov : N / 2 ≤ ghsPart N n (K + 1))
    (hE1 : ghsUniformError N n σ ≤ E)
    (hE2 : (N : ℝ) * (((Real.log ((n ^ 2 : ℕ) : ℝ) + Real.log 4)
              / Real.log ((N / n ^ 2 : ℕ) : ℝ)) * (Real.log N + Real.log 4)) ≤ E) :
    ‖∑ m ∈ Finset.Icc 1 N, f m‖
      ≤ (ghsRecursionError N
            + ((K + 1 : ℕ) : ℝ)
              * (E + (1 / (2 * Real.pi))
                  * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                      * ghsBlockConstOf σ ghsShapeConst))) / Real.log (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hn
  have hrest : (0 : ℝ) ≤ (1 / (2 * Real.pi))
      * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConstOf σ ghsShapeConst) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h1 : (0 : ℝ) ≤ dampedSize σ δ z N := dampedSize_nonneg hσ z N
    have h2 : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ σ := Real.rpow_nonneg (by positivity) σ
    have h3 : (0 : ℝ) ≤ ghsBlockConstOf σ ghsShapeConst := ghsBlockConstOf_nonneg _ _
    positivity
  refine norm_sum_Icc_le_ghs hcm hf hN (ghsPart_mono hN1 hn) (one_le_ghsPart hn)
    (ghsPart_zero N n) (K + 1) hcov ?_
  intro k hk
  match k, hk with
  | 0, _ =>
      -- the small primes
      have h0 : ghsPart N n 0 = 1 := ghsPart_zero N n
      have h1 : ghsPart N n 1 = n ^ 2 := ghsPart_one hN1 hn
      rw [h0, h1, Nat.div_one]
      refine le_trans (norm_sum_Icc_ghs_small_block_le hf hn2 hPN hNP hN1 le_rfl) ?_
      linarith [hE2, hrest]
  | 1, _ =>
      -- the trimmed block
      have h1 : ghsPart N n 1 = n ^ 2 := ghsPart_one hN1 hn
      have h2 : ghsPart N n 2 = ghsBlockRight N 0 := by
        rw [ghsPart_succ, ghsBlockRight_eq_left_succ] at *
        exact max_eq_right hA0
      rw [h1, h2]
      refine le_trans (ghs_block_D_trimmed_explicit hf1 hmul hf hσ hz hδ hunif hn hne hN1
        (by simpa using hthr 0 (by omega)) (hBN 0 (by omega)) hA0
        (by simpa using hheight 0 (by omega))) ?_
      have hle : ghsPerronError N (ghsBlockRight N 0) (N / n ^ 2) n σ ≤ E :=
        le_trans (ghsPerronError_le_uniform hN1 (Nat.div_le_self _ _) (Nat.div_le_self _ _)) hE1
      linarith [hle]
  | (j + 2), hk =>
      -- the geometric block of index `j + 1`
      have hjK : j + 1 < K := by omega
      have hA1 : n ^ 2 ≤ ghsBlockLeft N (j + 1) := hAk (j + 1) (by omega) hjK
      have hA2 : n ^ 2 ≤ ghsBlockLeft N (j + 2) :=
        le_trans hA1 (ghsBlockLeft_mono hN1 (Nat.le_succ (j + 1)))
      have hpa : ghsPart N n (j + 2) = ghsBlockLeft N (j + 1) := ghsPart_succ_eq hA1
      have hpb : ghsPart N n (j + 3) = ghsBlockRight N (j + 1) := by
        rw [ghsBlockRight_eq_left_succ]
        exact ghsPart_succ_eq hA2
      rw [show j + 2 + 1 = j + 3 from rfl, hpa, hpb]
      refine le_trans (ghs_block_D_geometric_explicit hf1 hmul hf hσ hz hδ hunif hn hne hN1
        (by omega) (hthr (j + 1) hjK) (hBN (j + 1) hjK) hA1 (hheight (j + 1) hjK)) ?_
      have hle : ghsPerronError N (ghsBlockRight N (j + 1)) (N / ghsBlockLeft N (j + 1)) n σ ≤ E :=
        le_trans (ghsPerronError_le_uniform hN1 (Nat.div_le_self _ _) (Nat.div_le_self _ _)) hE1
      linarith [hle]

end RHTower.Sieve

end
