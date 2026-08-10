import GaloisForLFunctions.RHTower.Sieve.GhsUniformErrorBound

/-!
# The small-prime block costs `N·log log N`

The block `(1, n²]` is bounded by `N·((log n² + log 4)/log⌊N/n²⌋)·(log N + log 4)`.  At the height
`ghsHeight N ≤ 2(log N)⁶` the numerator is `≍ log log N`, and the denominator is large: `n²` sits
below `ghsScale N 1`, whose complement `⌊N/n²⌋` therefore exceeds `ghsScale N 1 ≍ N^{1/2}`, so

```text
log⌊N/n²⌋ ≥ (log N)/2 − log 2 ≥ (log N)/4 .
```

The last factor is at most `2 log N`, and the two powers of `log N` cancel:

```text
small block ≤ N·(32 log 2 + 96 log log N) .
```

So `K` of them, divided by `N·log N`, is `≍ (log log N)²/log N → 0`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- **The small-prime block is `N·log log N`.** -/
theorem ghs_small_block_le {N : ℕ} (hlogN : (3 : ℝ) ≤ Real.log N) (hN16 : 16 ≤ N)
    (hroot : (ghsHeight N) ^ 2 ≤ ghsScale N 1) :
    (N : ℝ) * (((Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
            / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ)) * (Real.log N + Real.log 4))
      ≤ (N : ℝ) * (32 * Real.log 2 + 96 * Real.log (Real.log N)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set L : ℝ := Real.log N with hLdef
  have hL : (3 : ℝ) ≤ L := hlogN
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by linarith)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  -- the numerator
  have hone : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ (by linarith)
  have hhup : ((ghsHeight N : ℕ) : ℝ) ≤ 2 * L ^ 6 := ghsHeight_le hone
  have hhlow : (1 : ℝ) ≤ ((ghsHeight N : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ ghsHeight N := by rw [ghsHeight]; omega
    exact_mod_cast this
  have hlogh : Real.log ((ghsHeight N : ℕ) : ℝ) ≤ Real.log 2 + 6 * Real.log L := by
    have hstep : Real.log ((ghsHeight N : ℕ) : ℝ) ≤ Real.log (2 * L ^ 6) :=
      Real.log_le_log (by linarith) hhup
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hstep
    push_cast at hstep
    linarith
  have hnum : Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4
      ≤ 4 * Real.log 2 + 12 * Real.log L := by
    have hcast : (((ghsHeight N) ^ 2 : ℕ) : ℝ) = ((ghsHeight N : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [hcast, Real.log_pow, hlog4]
    push_cast
    linarith [hlogh]
  have hnum0 : (0 : ℝ) ≤ Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4 := by
    have h1 : (0 : ℝ) ≤ Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  -- the denominator
  have hcomp : ghsScale N 1 ≤ N / ghsScale N 1 := by
    have := ghsScale_le_ghsBlockRight_zero (N := N) (by omega)
    have hrw : ghsBlockRight N 0 = N / ghsScale N 1 := by norm_num [ghsBlockRight]
    rwa [hrw] at this
  have hhpos : 0 < (ghsHeight N) ^ 2 := by
    have : 0 < ghsHeight N := by rw [ghsHeight]; omega
    exact pow_pos this 2
  have hdvd : ghsScale N 1 ≤ N / (ghsHeight N) ^ 2 :=
    le_trans hcomp (Nat.div_le_div_left hroot hhpos)
  have hdvdR : ((ghsScale N 1 : ℕ) : ℝ) ≤ ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hdvd
  have hk1 : (2 : ℝ) ^ (1 : ℕ) * Real.log 2 ≤ L := by norm_num; linarith
  have hs2 : 2 ≤ ghsScale N 1 := ghsScale_pos (by omega) hk1
  have hs2R : (2 : ℝ) ≤ ((ghsScale N 1 : ℕ) : ℝ) := by exact_mod_cast hs2
  have hscalelog : L / 2 - Real.log 2 ≤ Real.log ((ghsScale N 1 : ℕ) : ℝ) := by
    have := le_log_ghsScale (N := N) (k := 1) (by omega) hk1
    norm_num at this
    linarith
  have hden : L / 4 ≤ Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) := by
    have hstep : Real.log ((ghsScale N 1 : ℕ) : ℝ)
        ≤ Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hdvdR
    linarith [hscalelog, hstep]
  have hden0 : (0 : ℝ) < L / 4 := by linarith
  -- the last factor
  have hlast : L + Real.log 4 ≤ 2 * L := by rw [hlog4]; linarith
  have hlast0 : (0 : ℝ) ≤ L + Real.log 4 := by rw [hlog4]; linarith
  -- assemble
  have hq : (Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
        / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ)
      ≤ (4 * Real.log 2 + 12 * Real.log L) / (L / 4) := by
    have hnum'0 : (0 : ℝ) ≤ 4 * Real.log 2 + 12 * Real.log L := by linarith
    calc (Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
          / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ)
        ≤ (4 * Real.log 2 + 12 * Real.log L)
            / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ (4 * Real.log 2 + 12 * Real.log L) / (L / 4) :=
          div_le_div_of_nonneg_left hnum'0 hden0 hden
  have hq0 : (0 : ℝ) ≤ (Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
      / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) := by
    have hd0 : (0 : ℝ) ≤ Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ) := by linarith
    exact div_nonneg hnum0 hd0
  refine mul_le_mul_of_nonneg_left ?_ hN0
  have hprod : ((Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
          / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ)) * (L + Real.log 4)
      ≤ ((4 * Real.log 2 + 12 * Real.log L) / (L / 4)) * (2 * L) := by
    have hA : ((Real.log (((ghsHeight N) ^ 2 : ℕ) : ℝ) + Real.log 4)
            / Real.log ((N / (ghsHeight N) ^ 2 : ℕ) : ℝ)) * (L + Real.log 4)
        ≤ ((4 * Real.log 2 + 12 * Real.log L) / (L / 4)) * (L + Real.log 4) :=
      mul_le_mul_of_nonneg_right hq hlast0
    have hB0 : (0 : ℝ) ≤ (4 * Real.log 2 + 12 * Real.log L) / (L / 4) := by
      have : (0 : ℝ) ≤ 4 * Real.log 2 + 12 * Real.log L := by linarith
      positivity
    have hB : ((4 * Real.log 2 + 12 * Real.log L) / (L / 4)) * (L + Real.log 4)
        ≤ ((4 * Real.log 2 + 12 * Real.log L) / (L / 4)) * (2 * L) :=
      mul_le_mul_of_nonneg_left hlast hB0
    linarith [hA, hB]
  have hval : ((4 * Real.log 2 + 12 * Real.log L) / (L / 4)) * (2 * L)
      = 32 * Real.log 2 + 96 * Real.log L := by
    field_simp
    ring
  linarith [hprod, hval.le, hval.ge]

end RHTower.Sieve

end
