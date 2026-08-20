import GaloisForLFunctions.RHTower.Sieve.ExceptionalMomentOrder
import GaloisForLFunctions.RHTower.Sieve.ScheduleMonomialLimits
import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule

/-!
# The exceptional half at the growing moment order

Putting the two exponents of `Sieve/ExceptionalMomentOrder` at the schedule.  The ladder starts at
`exp((log x)^{a₀})`, so every block has

```text
   g_j = log( #B_j·θ²/k )  ≥  (log x)^{a₀}/2 ,
   g_j − n_j              ≥  −D·log log x ,
```

the first because `#B_j ≍ R_j·η/log R_j` and `R_j ≥ exp((log x)^{a₀})`, the second because
`NA_j/#B_j ≍ log NA_j/η` is only polylogarithmic.  Choosing

```text
   k ≥ 2(log x)^{1−a₀}
```

makes `k·g_j ≥ log x`, so the trivial term is below `W/x`, while the diagonal term costs only
`exp(k·D·log log x) = exp(O((log x)^{1−a₀}·log log x)) = x^{o(1)}`.

**Both bounds fail for a bounded `k`, and the second fails for `k ≫ log x/log log x`** — the moment
order is pinned from both sides, and only an exponentially high ladder bottom leaves a window.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory

noncomputable section

/-- **The growing moment order kills the trivial term.** -/
theorem exp_neg_mul_le_inv {a₀ x g₀ : ℝ} (hx : 1 < x) {k : ℕ}
    (hk : 2 * (Real.log x) ^ (1 - a₀) ≤ (k : ℝ)) (hg : (Real.log x) ^ a₀ / 2 ≤ g₀) :
    Real.exp (-((k : ℝ) * g₀)) ≤ 1 / x := by
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hpa : (0 : ℝ) < (Real.log x) ^ a₀ := Real.rpow_pos_of_pos hlogx a₀
  have hp1a : (0 : ℝ) < (Real.log x) ^ (1 - a₀) := Real.rpow_pos_of_pos hlogx (1 - a₀)
  have hg0 : (0 : ℝ) < g₀ := lt_of_lt_of_le (by positivity) hg
  have hprod : (Real.log x) ^ (1 - a₀) * (Real.log x) ^ a₀ = Real.log x := by
    rw [← Real.rpow_add hlogx, show 1 - a₀ + a₀ = (1 : ℝ) by ring, Real.rpow_one]
  have hkg : Real.log x ≤ (k : ℝ) * g₀ := by
    have h1 : 2 * (Real.log x) ^ (1 - a₀) * ((Real.log x) ^ a₀ / 2) ≤ (k : ℝ) * g₀ := by
      have hstep := mul_le_mul hk hg (by positivity) (by positivity)
      exact hstep
    nlinarith [h1, hprod]
  have hinv : (1 : ℝ) / x = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
  rw [hinv]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The exceptional half of the annulus at a growing moment order.** -/
theorem measureReal_annulusLarge_le_growing {P : Finset ℕ} {R η θ W w₀ nmax D a₀ x : ℝ} {L k : ℕ}
    (hR : 0 < R) (hη : 0 ≤ η) (hk : 1 ≤ k) (hW : 0 ≤ W) (hθ : 0 < θ) (hnmax : 0 ≤ nmax)
    (hx : 1 < x) (_hD : 0 ≤ D) (_hll : 0 ≤ Real.log (Real.log x))
    (hPprime : ∀ p ∈ P, p.Prime)
    (hNA : ∀ j ∈ Finset.range L, 1 ≤ ⌊R * (1 + η) ^ (j + 1)⌋₊)
    (hcard : ∀ j ∈ Finset.range L, 0 < ((geomBlock P R (1 + η) j).card : ℝ))
    (hkbig : 2 * (Real.log x) ^ (1 - a₀) ≤ (k : ℝ))
    (hg : ∀ j ∈ Finset.range L, (Real.log x) ^ a₀ / 2
      ≤ Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ 2 / (k : ℝ)))
    (hn : ∀ j ∈ Finset.range L, Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ nmax)
    (hd : ∀ j ∈ Finset.range L, -(D * Real.log (Real.log x))
      ≤ Real.log (((geomBlock P R (1 + η) j).card : ℝ) * θ ^ 2 / (k : ℝ))
        - Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ)) :
    volume.real (annulusLarge
        (allBlocksSmall P R η L
          (fun j => ((geomBlock P R (1 + η) j).card : ℝ) * θ) W) W w₀)
      ≤ (L : ℝ) * (2 * W / x
          + 2 * (1 + (k : ℝ) * nmax)
            * Real.exp ((k : ℝ) * (D * Real.log (Real.log x)))) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hbase := measureReal_annulusLarge_le_exp (P := P) (R := R) (η := η) (θ := θ) (W := W)
    (w₀ := w₀) (g₀ := (Real.log x) ^ a₀ / 2) (d := -(D * Real.log (Real.log x))) (nmax := nmax)
    (L := L) (k := k) hR hη hk hW hθ hnmax hPprime hNA hcard hg hn hd
  refine hbase.trans ?_
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hL0
  have h1 : 2 * W * Real.exp (-((k : ℝ) * ((Real.log x) ^ a₀ / 2))) ≤ 2 * W / x := by
    have := exp_neg_mul_le_inv (a₀ := a₀) (x := x) (g₀ := (Real.log x) ^ a₀ / 2) hx hkbig
      (le_refl _)
    have hmul := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 2 * W)
    calc 2 * W * Real.exp (-((k : ℝ) * ((Real.log x) ^ a₀ / 2))) ≤ 2 * W * (1 / x) := hmul
      _ = 2 * W / x := by ring
  have h2 : Real.exp (-((k : ℝ) * -(D * Real.log (Real.log x))))
      = Real.exp ((k : ℝ) * (D * Real.log (Real.log x))) := by
    congr 1
    ring
  rw [h2]
  linarith [h1]

/-- **The diagonal cost of a growing moment order is `x^{o(1)}`.** -/
theorem tendsto_expSubLinear_div_rpow {a₀ D e s : ℝ} (ha₀0 : 0 < a₀) (_ha₀1 : a₀ < 1)
    (hD : 0 ≤ D) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (Real.log x) ^ e
        * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x)) / x ^ s)
      atTop (𝓝 0) := by
  have hmaj := tendsto_logRpow_mul_expSaving (d := (1 : ℝ)) (s := s / 2) (by norm_num)
    (by linarith) e
  have hsmall := tendsto_logMonomial (e := -a₀) (by linarith) 1
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have h1 : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have h2 : (0 : ℝ) < x ^ s := Real.rpow_pos_of_pos (by linarith) s
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      Tendsto.eventually_le_const (show (0 : ℝ) < s / (2 * (D + 1)) by positivity) hsmall]
      with x hx1 hlog1 hsm
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hnn : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have hll : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    rw [pow_one] at hsm
    have hprod : (Real.log x) ^ (-a₀) * Real.log x = (Real.log x) ^ (1 - a₀) := by
      rw [show (1 : ℝ) - a₀ = -a₀ + 1 by ring, Real.rpow_add hlogx, Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_right hsm hlogx.le
    have hid : (Real.log x) ^ (-a₀) * Real.log (Real.log x) * Real.log x
        = (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) := by
      rw [← hprod]
      ring
    rw [hid] at hmul
    have hDfrac : D * (s / (2 * (D + 1))) ≤ s / 2 := by
      have hpos : (0 : ℝ) < 2 * (D + 1) := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hD, hs]
    have hkey : D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) ≤ s / 2 * Real.log x := by
      nlinarith [hmul, hD, hlogx, hDfrac]
    have hxs : x ^ s = Real.exp (s * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0]
      congr 1
      ring
    rw [hxs]
    have hdiv : (Real.log x) ^ e * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x))
          / Real.exp (s * Real.log x)
        = (Real.log x) ^ e
          * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) - s * Real.log x) := by
      rw [Real.exp_sub]
      ring
    rw [hdiv]
    have hexple : Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) - s * Real.log x)
        ≤ Real.exp (-(s / 2 * (Real.log x) ^ (1 : ℝ))) := by
      rw [Real.rpow_one]
      exact Real.exp_le_exp.2 (by linarith)
    exact mul_le_mul_of_nonneg_left hexple hnn

end

end RHTower.Sieve
