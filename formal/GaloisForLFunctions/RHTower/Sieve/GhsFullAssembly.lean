import GaloisForLFunctions.RHTower.Sieve.GhsTrivialBlock

/-!
# The partition that reaches `N/2`

Appending `N` to the trimmed partition gives a family of endpoints that satisfies the capstone's
coverage condition:

```text
ghsPartTop N n K j = if j ≤ K + 1 then ghsPart N n j else N .
```

Its blocks are the small `(1, n²]`, the trimmed `(n², ghsBlockRight N 0]`, the geometric
`(A_k, B_k]` for `1 ≤ k < K`, and the top `(ghsPart N n (K+1), N]`.  The top block is where the
geometric threshold stops and the trivial bound of `GhsTrivialBlock` takes over; the outer weights
there have bounded `1/p`-mass by Mertens' first theorem on a block, so it costs `O(N)`.

The result is the Granville–Harper–Soundararajan mean value with no hypothesis about any block:
everything is a condition on `N`, the height `n`, the abscissa `σ`, the distance data `z, δ`, the
number of scales `K`, and the two error levels.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The trimmed partition with `N` appended. -/
def ghsPartTop (N n K : ℕ) (j : ℕ) : ℕ := if j ≤ K + 1 then ghsPart N n j else N

theorem ghsPartTop_eq {N n K j : ℕ} (h : j ≤ K + 1) :
    ghsPartTop N n K j = ghsPart N n j := if_pos h

theorem ghsPartTop_zero (N n K : ℕ) : ghsPartTop N n K 0 = 1 := by
  rw [ghsPartTop_eq (Nat.zero_le _), ghsPart_zero]

theorem ghsPartTop_top {N n K j : ℕ} (h : ¬ j ≤ K + 1) :
    ghsPartTop N n K j = N := if_neg h

/-- Every endpoint of the trimmed partition is at most `N`. -/
theorem ghsPart_le {N n j : ℕ} (hN : 1 ≤ N) (hn2 : n ^ 2 ≤ N) : ghsPart N n j ≤ N := by
  cases j with
  | zero => rw [ghsPart_zero]; omega
  | succ i => rw [ghsPart_succ]; exact max_le hn2 ghsBlockLeft_le

theorem one_le_ghsPartTop {N n K : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (j : ℕ) :
    1 ≤ ghsPartTop N n K j := by
  rw [ghsPartTop]
  split_ifs with h
  · exact one_le_ghsPart hn j
  · exact hN

theorem ghsPartTop_mono {N n K : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) (hn2 : n ^ 2 ≤ N) :
    Monotone (ghsPartTop N n K) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [ghsPartTop, ghsPartTop]
  split_ifs with h1 h2 h2
  · exact ghsPart_mono hN hn (Nat.le_succ j)
  · exact ghsPart_le hN hn2
  · omega
  · exact le_rfl

/-- **The Granville–Harper–Soundararajan mean value over the full partition.** -/
theorem norm_sum_Icc_le_ghs_full
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
    (hE1 : ghsUniformError N n σ ≤ E)
    (hE2 : (N : ℝ) * (((Real.log ((n ^ 2 : ℕ) : ℝ) + Real.log 4)
              / Real.log ((N / n ^ 2 : ℕ) : ℝ)) * (Real.log N + Real.log 4)) ≤ E)
    (hE3 : (N : ℝ) * (((1 / Real.log 2)
              * (Real.log (N : ℝ) - Real.log ((ghsPart N n (K + 1) : ℕ) : ℝ)
                  + mertensBlockGapConst))
            * (Real.log ((N / ghsPart N n (K + 1) : ℕ) : ℝ) + Real.log 4)) ≤ E) :
    ‖∑ m ∈ Finset.Icc 1 N, f m‖
      ≤ (ghsRecursionError N
            + ((K + 2 : ℕ) : ℝ)
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
  have hcov : N / 2 ≤ ghsPartTop N n K (K + 2) := by
    rw [ghsPartTop_top (by omega)]
    omega
  refine norm_sum_Icc_le_ghs hcm hf hN (ghsPartTop_mono hN1 hn hPN)
    (one_le_ghsPartTop hn hN1) (ghsPartTop_zero N n K) (K + 2) hcov ?_
  intro k hk
  by_cases htop : k = K + 1
  · -- the top of the range
    subst htop
    rw [ghsPartTop_eq (le_rfl), ghsPartTop_top (by omega)]
    refine le_trans (norm_sum_Icc_ghs_block_trivial_le hf (one_le_ghsPart hn (K + 1))
      (ghsPart_le hN1 hPN) le_rfl
      (Nat.div_pos (ghsPart_le hN1 hPN) (one_le_ghsPart hn (K + 1)))
      (Nat.div_le_self _ _)) ?_
    linarith [hE3, hrest]
  · have hk' : k < K + 1 := by omega
    rw [ghsPartTop_eq (by omega), ghsPartTop_eq (by omega)]
    match k, hk' with
    | 0, _ =>
        have h0 : ghsPart N n 0 = 1 := ghsPart_zero N n
        have h1 : ghsPart N n 1 = n ^ 2 := ghsPart_one hN1 hn
        rw [h0, h1, Nat.div_one]
        refine le_trans (norm_sum_Icc_ghs_small_block_le hf hn2 hPN hNP hN1 le_rfl) ?_
        linarith [hE2, hrest]
    | 1, _ =>
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
    | (j + 2), hj =>
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
        have hle : ghsPerronError N (ghsBlockRight N (j + 1))
            (N / ghsBlockLeft N (j + 1)) n σ ≤ E :=
          le_trans (ghsPerronError_le_uniform hN1 (Nat.div_le_self _ _) (Nat.div_le_self _ _)) hE1
        linarith [hle]

end RHTower.Sieve

end
