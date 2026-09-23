import GaloisForLFunctions.RHTower.Sieve.ShortExceptionalMeasure

/-!
# The moment method at a growing order

`Sieve/ShortExceptionalMeasure` bounds one block's exceptional set by

```text
   (2π)⁻¹·2·( 2πW + 4·NA^k(1 + log NA^k) )·( k/(#B·θ²) )^k .
```

Both `NA^k` and the saving are exponential in `k`, so the estimate is only usable in the form

```text
   |𝒰_j|  ≤  2W·e^{−k·g_j}  +  2(1 + k·n_j)·e^{−k·(g_j − n_j)} ,
   g_j = log( #B_j·θ² / k ) ,   n_j = log NA_j ,
```

where the two exponents must be balanced **against each other**: `g_j` alone controls the trivial
term `W`, while the difference `g_j − n_j` — which is *negative*, of size `−O(log log x)` once the
block is known to hold `≍ NA_j·η/log NA_j` primes — controls the diagonal term.  Since `g_j` is of
size `log NA_j` and `W ≍ x^{1/2}`, killing the first term costs `k ≍ log x / log NA_min`: the moment
order cannot be a constant, and it is bounded above by the second term through
`k·(n_j − g_j) = O(k·log log x)`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The moment saving in exponential form. -/
theorem momentSaving_eq {k : ℕ} (hk : 1 ≤ k) {Θ : ℝ} (hΘ : 0 < Θ) :
    ((k : ℝ) / Θ) ^ k = Real.exp (-((k : ℝ) * Real.log (Θ / (k : ℝ)))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((k : ℝ) / Θ) ^ k := by positivity
  rw [← Real.exp_log hpos, Real.log_pow]
  congr 1
  rw [Real.log_div (ne_of_gt hk0) (ne_of_gt hΘ), Real.log_div (ne_of_gt hΘ) (ne_of_gt hk0)]
  ring

/-- The `k`-th power of the ladder top in exponential form. -/
theorem natPow_cast_eq_exp {NA k : ℕ} (hNA : 1 ≤ NA) :
    ((NA ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log ((NA : ℕ) : ℝ)) := by
  have hNA0 : (0 : ℝ) < ((NA : ℕ) : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hNA
  push_cast
  rw [← Real.exp_log (show (0 : ℝ) < ((NA : ℕ) : ℝ) ^ k by positivity), Real.log_pow]

theorem log_natPow_cast {NA k : ℕ} (hNA : 1 ≤ NA) :
    Real.log ((NA ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log ((NA : ℕ) : ℝ) := by
  have hNA0 : (0 : ℝ) < ((NA : ℕ) : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hNA
  push_cast
  rw [Real.log_pow]

/-- **One block's exceptional measure, with the two exponents separated.** -/
theorem measureReal_shortExceptional_le_exp {B : Finset ℕ} {NA k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hk : 1 ≤ k) (hNA : 1 ≤ NA)
    {W θ g n : ℝ} (hW : 0 ≤ W) (hθ : 0 < θ) (hcard : 0 < (B.card : ℝ))
    (hg : g ≤ Real.log ((B.card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ)))
    (hn : Real.log ((NA : ℕ) : ℝ) ≤ n) :
    volume.real (shortExceptional B W ((B.card : ℝ) * θ))
      ≤ 2 * W * Real.exp (-((k : ℝ) * g))
        + 2 * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * (g - n))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hΘ : (0 : ℝ) < (B.card : ℝ) * θ ^ (2 : ℕ) := by positivity
  have hNA0 : (0 : ℝ) < ((NA : ℕ) : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hNA
  have hlogNA : (0 : ℝ) ≤ Real.log ((NA : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hNA)
  have hn0 : (0 : ℝ) ≤ n := le_trans hlogNA hn
  -- the saving
  have hS : ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k ≤ Real.exp (-((k : ℝ) * g)) := by
    rw [momentSaving_eq hk hΘ]
    exact Real.exp_le_exp.2 (by nlinarith [hg, hk0])
  have hS0 : (0 : ℝ) ≤ ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k := by positivity
  -- the diagonal factor
  have hpow : ((NA ^ k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log ((NA : ℕ) : ℝ)) :=
    natPow_cast_eq_exp hNA
  have hlogpow : Real.log ((NA ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log ((NA : ℕ) : ℝ) :=
    log_natPow_cast hNA
  have hdiag : 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
        * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k
      ≤ 4 * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * (g - n))) := by
    have hA : ((NA ^ k : ℕ) : ℝ) ≤ Real.exp ((k : ℝ) * n) := by
      rw [hpow]
      exact Real.exp_le_exp.2 (by nlinarith [hn, hk0])
    have hB' : 1 + Real.log ((NA ^ k : ℕ) : ℝ) ≤ 1 + (k : ℝ) * n := by
      rw [hlogpow]
      nlinarith [hn, hk0]
    have hA0 : (0 : ℝ) ≤ ((NA ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ 1 + Real.log ((NA ^ k : ℕ) : ℝ) := by
      rw [hlogpow]
      nlinarith [hlogNA, hk0]
    have hstep : 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
          * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k
        ≤ 4 * Real.exp ((k : ℝ) * n) * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * g)) := by
      have h1 : 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
          ≤ 4 * Real.exp ((k : ℝ) * n) * (1 + (k : ℝ) * n) := by
        nlinarith [hA, hB', hA0, hB0, Real.exp_pos ((k : ℝ) * n)]
      have h2 : (0 : ℝ) ≤ 4 * Real.exp ((k : ℝ) * n) * (1 + (k : ℝ) * n) := by
        have : (0 : ℝ) ≤ 1 + (k : ℝ) * n := by nlinarith [hn0, hk0]
        positivity
      nlinarith [h1, h2, hS, hS0,
        mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * ((NA ^ k : ℕ) : ℝ)) hB0]
    refine hstep.trans (le_of_eq ?_)
    have hexp : Real.exp ((k : ℝ) * n) * Real.exp (-((k : ℝ) * g))
        = Real.exp (-((k : ℝ) * (g - n))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 4 * Real.exp ((k : ℝ) * n) * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * g))
        = 4 * (1 + (k : ℝ) * n) * (Real.exp ((k : ℝ) * n) * Real.exp (-((k : ℝ) * g))) := by ring
      _ = 4 * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * (g - n))) := by rw [hexp]
  -- assemble
  refine (measureReal_shortExceptional_le_relative hBprime hB hk hW hθ hcard).trans ?_
  have hsplit : (2 * Real.pi)⁻¹
        * (2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k)
      = 2 * W * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k
        + (2 * Real.pi)⁻¹ * (2 * (4 * ((NA ^ k : ℕ) : ℝ)
            * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
              * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k)) := by
    field_simp
  rw [hsplit]
  have hfirst : 2 * W * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k
      ≤ 2 * W * Real.exp (-((k : ℝ) * g)) :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have hsecond : (2 * Real.pi)⁻¹ * (2 * (4 * ((NA ^ k : ℕ) : ℝ)
        * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k))
      ≤ 2 * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * (g - n))) := by
    have hcoef : (2 * Real.pi)⁻¹ * 2 ≤ 1 / 2 := by
      rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hpi2]
    have hD0 : (0 : ℝ) ≤ 4 * (1 + (k : ℝ) * n) * Real.exp (-((k : ℝ) * (g - n))) := by
      have : (0 : ℝ) ≤ 1 + (k : ℝ) * n := by nlinarith [hn0, hk0]
      positivity
    have hval : (2 * Real.pi)⁻¹ * (2 * (4 * ((NA ^ k : ℕ) : ℝ)
          * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k))
        = ((2 * Real.pi)⁻¹ * 2) * (4 * ((NA ^ k : ℕ) : ℝ)
          * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k) := by
      ring
    rw [hval]
    have hpos : (0 : ℝ) ≤ 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
        * ((k : ℝ) / ((B.card : ℝ) * θ ^ (2 : ℕ))) ^ k := by
      have hB0 : (0 : ℝ) ≤ 1 + Real.log ((NA ^ k : ℕ) : ℝ) := by
        rw [hlogpow]
        nlinarith [hlogNA, hk0]
      have : (0 : ℝ) ≤ 4 * ((NA ^ k : ℕ) : ℝ) := by positivity
      have := mul_nonneg this hB0
      exact mul_nonneg this hS0
    nlinarith [hcoef, hdiag, hpos, hD0, (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * 2)]
  linarith

/-- **The exceptional half of the annulus at a growing moment order.**  The two exponents are
uniformised separately: `g₀` bounds every `g_j` from below, `d` bounds every difference
`g_j − n_j` from below, and `nmax` bounds every `n_j` from above. -/
theorem measureReal_annulusLarge_le_exp {P : Finset ℕ} {R η θ W w₀ g₀ d nmax : ℝ} {L k : ℕ}
    (hR : 0 < R) (hη : 0 ≤ η) (hk : 1 ≤ k) (hW : 0 ≤ W) (hθ : 0 < θ) (_hnmax : 0 ≤ nmax)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hNA : ∀ j ∈ Finset.range L, 1 ≤ ⌊R * (1 + η) ^ (j + 1)⌋₊)
    (hcard : ∀ j ∈ Finset.range L, 0 < ((geomBlock P R (1 + η) j).card : ℝ))
    (hg : ∀ j ∈ Finset.range L,
      g₀ ≤ Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ)))
    (hn : ∀ j ∈ Finset.range L,
      Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ nmax)
    (hd : ∀ j ∈ Finset.range L,
      d ≤ Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ))
        - Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ)) :
    volume.real (annulusLarge
        (allBlocksSmall P R η L
          (fun j => ((geomBlock P R (1 + η) j).card : ℝ) * θ) W) W w₀)
      ≤ (L : ℝ) * (2 * W * Real.exp (-((k : ℝ) * g₀))
          + 2 * (1 + (k : ℝ) * nmax) * Real.exp (-((k : ℝ) * d))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine (measureReal_annulusLarge_le P R η L
    (fun j => ((geomBlock P R (1 + η) j).card : ℝ) * θ) W w₀).trans ?_
  have hterm : ∀ j ∈ Finset.range L,
      volume.real (shortExceptional (geomBlock P R (1 + η) j) W
          (((geomBlock P R (1 + η) j).card : ℝ) * θ))
        ≤ 2 * W * Real.exp (-((k : ℝ) * g₀))
          + 2 * (1 + (k : ℝ) * nmax) * Real.exp (-((k : ℝ) * d)) := by
    intro j hj
    set nj : ℝ := Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) with hnjdef
    have hbase := measureReal_shortExceptional_le_exp
      (B := geomBlock P R (1 + η) j) (NA := ⌊R * (1 + η) ^ (j + 1)⌋₊) (k := k)
      (fun p hp => hPprime p (geomBlock_subset P R (1 + η) j hp))
      (geomBlock_subset_Icc_one hR hη j) hk (hNA j hj) hW hθ (hcard j hj)
      (le_refl _) (le_refl nj)
    refine hbase.trans ?_
    have hnj0 : (0 : ℝ) ≤ nj := by
      rw [hnjdef]
      refine Real.log_nonneg ?_
      exact_mod_cast hNA j hj
    have h1 : Real.exp (-((k : ℝ)
          * Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ))))
        ≤ Real.exp (-((k : ℝ) * g₀)) :=
      Real.exp_le_exp.2 (by nlinarith [hg j hj, hk0])
    have h2 : Real.exp (-((k : ℝ)
          * (Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ)) - nj)))
        ≤ Real.exp (-((k : ℝ) * d)) :=
      Real.exp_le_exp.2 (by nlinarith [hd j hj, hk0])
    have h3 : 1 + (k : ℝ) * nj ≤ 1 + (k : ℝ) * nmax := by
      have := hn j hj
      nlinarith [hk0]
    have hE0 : (0 : ℝ) < Real.exp (-((k : ℝ) * d)) := Real.exp_pos _
    have hnn : (0 : ℝ) ≤ 1 + (k : ℝ) * nj := by nlinarith [hnj0, hk0]
    nlinarith [h1, h2, h3, hE0, hnn, hW,
      Real.exp_pos (-((k : ℝ)
        * (Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ (2 : ℕ) / (k : ℝ)) - nj)))]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end RHTower.Sieve
