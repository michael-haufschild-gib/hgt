import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaCapstone

/-!
# A wide order: a rectangle of width `(log log t)²/log t`

The rectangle estimate `norm_dirichlet_sigma_littlewood_capstone` is valid on the strip
`1 - σ ≤ 1/(6·2^K)` for any order `K` clearing the largeness condition.  The order chosen in
`DirichletOrderChoice` is the *largest* admissible one, which optimises the estimate on the line but
makes the strip as narrow as possible, `≍ 1/log t`.

A zero-free region argument wants the opposite trade.  Landau's lemma converts a growth bound `Φ` on
a disc of radius `R` into a remainder `16 log Φ / R`, so the useful quantity is

```text
log Φ / (strip width) ,
```

and widening the strip by a factor `W` costs only `C^{(1-σ)}` in the head, i.e. `W·(log t)/K` in the
logarithm.  With

```text
2^K ≍ L/(log L)²,      L = log(t/2π),
```

the width is `≍ (log L)²/L`, the head factor is `exp(O(log L)) = (log t)^{O(1)}`, and the ratio is
`≍ L/log L = log t/log log t` — the Littlewood exponent, where the narrow strip gives only `log t`.

This module fixes that order.  `wideOrder t` is the greatest `K` with

```text
30·2^K·(log L)²  ≤  L ,
```

so that `L/(60 (log L)²) < 2^(wideOrder t) ≤ L/(30 (log L)²)`, and the strip half-width
`wideEta t = 1/(6·2^(wideOrder t))` is pinned between `5(log L)²/L` and `10(log L)²/L`.
-/

namespace RHTower.Sieve

open Finset

/-- The logarithmic scale `L = log(t/2π)` of the Dirichlet-partial-sum chain. -/
noncomputable def wideScale (t : ℝ) : ℝ := Real.log (t / (2 * Real.pi))

/-- **The wide order.**  The greatest `K` whose strip `1 - σ ≤ 1/(6·2^K)` is at least
`5(log L)²/L` wide. -/
noncomputable def wideOrder (t : ℝ) : ℕ :=
  Nat.findGreatest
    (fun K => 30 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t)
    ⌈wideScale t⌉₊

/-- The half-width of the wide strip. -/
noncomputable def wideEta (t : ℝ) : ℝ := 1 / (6 * (2 : ℝ) ^ wideOrder t)

/-! ### Two elementary logarithm bounds -/

/-- `log x ≤ 2√x`. -/
theorem wide_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h1
  linarith

/-- `(log x)² ≤ 16√x`. -/
theorem wide_log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ (2 : ℕ) ≤ 16 * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set u : ℝ := Real.sqrt x with hu
  have hu0 : 0 < u := Real.sqrt_pos.mpr hx0
  have husq : u ^ (2 : ℕ) = x := Real.sq_sqrt hx0.le
  have hlogu : Real.log u ≤ 2 * Real.sqrt u := wide_log_le_two_sqrt hu0
  have hlogx : Real.log x = 2 * Real.log u := by
    rw [hu, Real.log_sqrt hx0.le]; ring
  have hv : Real.sqrt u ^ (2 : ℕ) = u := Real.sq_sqrt hu0.le
  have hnn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hle : Real.log x ≤ 4 * Real.sqrt u := by rw [hlogx]; linarith
  have hsq : Real.log x ^ (2 : ℕ) ≤ (4 * Real.sqrt u) ^ (2 : ℕ) := by
    have h4 : 0 ≤ 4 * Real.sqrt u := by positivity
    nlinarith [hnn, hle]
  calc Real.log x ^ (2 : ℕ) ≤ (4 * Real.sqrt u) ^ (2 : ℕ) := hsq
    _ = 16 * u := by rw [mul_pow]; rw [hv]; ring
    _ = 16 * Real.sqrt x := by rw [hu]

/-! ### Admissibility -/

/-- Every order below `11` is admissible once `L ≥ 10¹²`. -/
theorem wide_admissible_of_le {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) {K : ℕ}
    (hK : (2 : ℝ) ^ K ≤ 2048) :
    30 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t := by
  set L : ℝ := wideScale t with hLdef
  have hL1 : (1 : ℝ) ≤ L := by nlinarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq := wide_log_sq_le hL1
  have hs : Real.sqrt L ^ (2 : ℕ) = L := Real.sq_sqrt hL0.le
  have hsnn : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsge : (10 : ℝ) ^ (6 : ℕ) ≤ Real.sqrt L := by
    nlinarith [hs, hsnn, hL]
  have hKpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  calc 30 * (2 : ℝ) ^ K * Real.log L ^ (2 : ℕ)
      ≤ 30 * (2 : ℝ) ^ K * (16 * Real.sqrt L) := by nlinarith [hsq, hKpos]
    _ = (480 * (2 : ℝ) ^ K) * Real.sqrt L := by ring
    _ ≤ ((10 : ℝ) ^ (6 : ℕ)) * Real.sqrt L := by nlinarith [hsnn, hK]
    _ ≤ Real.sqrt L * Real.sqrt L := by nlinarith [hsnn, hsge]
    _ = L := by nlinarith [hs]

/-- The search cap is not restrictive for the orders we use. -/
theorem wide_le_ceil {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) {K : ℕ}
    (hK : (K : ℝ) ≤ 2048) : K ≤ ⌈wideScale t⌉₊ := by
  have hL1 : (2048 : ℝ) ≤ wideScale t := by nlinarith
  have h1 : (K : ℝ) ≤ wideScale t := le_trans hK hL1
  have h2 : (K : ℝ) ≤ ((⌈wideScale t⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
  exact_mod_cast h2

/-- **The wide order is at least ten.** -/
theorem ten_le_wideOrder {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) : 10 ≤ wideOrder t := by
  refine Nat.le_findGreatest (wide_le_ceil hL (by norm_num)) ?_
  exact wide_admissible_of_le hL (K := 10) (by norm_num)

/-- **The wide order is admissible.** -/
theorem wideOrder_spec {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    30 * (2 : ℝ) ^ wideOrder t * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t := by
  refine Nat.findGreatest_spec
    (P := fun K => 30 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t)
    (m := 10) (wide_le_ceil hL (by norm_num)) ?_
  exact wide_admissible_of_le hL (K := 10) (by norm_num)

/-! ### The two-sided control of `2^(wideOrder t)` -/

/-- The upper bound: `30·2^K·(log L)² ≤ L`. -/
theorem two_pow_wideOrder_le {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    (2 : ℝ) ^ wideOrder t * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t / 30 := by
  have h := wideOrder_spec hL
  linarith

/-- `(log L)² ≥ 1` in the range of interest. -/
theorem one_le_log_wideScale_sq {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    (1 : ℝ) ≤ Real.log (wideScale t) ^ (2 : ℕ) := by
  have hL1 : (3 : ℝ) ≤ wideScale t := by nlinarith
  have h : (1 : ℝ) ≤ Real.log (wideScale t) := by
    have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  nlinarith

/-- A crude consequence: `2^K ≤ L/30`. -/
theorem two_pow_wideOrder_le_scale {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    (2 : ℝ) ^ wideOrder t ≤ wideScale t / 30 := by
  have h := two_pow_wideOrder_le hL
  have hlog := one_le_log_wideScale_sq hL
  have hpos : (0 : ℝ) < (2 : ℝ) ^ wideOrder t := by positivity
  nlinarith

/-- `K + 1` is still inside the search cap. -/
theorem wideOrder_succ_le_ceil {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    wideOrder t + 1 ≤ ⌈wideScale t⌉₊ := by
  have hle := two_pow_wideOrder_le_scale hL
  have hlt : ((wideOrder t : ℕ) : ℝ) < (2 : ℝ) ^ wideOrder t := by
    have := Nat.lt_two_pow_self (n := wideOrder t)
    exact_mod_cast this
  have h1 : ((wideOrder t : ℕ) : ℝ) + 1 ≤ wideScale t := by
    have hL30 : wideScale t / 30 + 1 ≤ wideScale t := by nlinarith
    linarith
  have h2 : ((wideOrder t : ℕ) : ℝ) + 1 ≤ ((⌈wideScale t⌉₊ : ℕ) : ℝ) :=
    le_trans h1 (Nat.le_ceil _)
  exact_mod_cast h2

/-- **The lower bound.**  The next order already fails, so `2^K` is within a factor two of the
target `L/(30(log L)²)`. -/
theorem lt_two_pow_wideOrder_succ {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    wideScale t < 30 * (2 : ℝ) ^ (wideOrder t + 1) * Real.log (wideScale t) ^ (2 : ℕ) := by
  have hnot := Nat.findGreatest_is_greatest
    (P := fun K => 30 * (2 : ℝ) ^ K * Real.log (wideScale t) ^ (2 : ℕ) ≤ wideScale t)
    (k := wideOrder t + 1) (n := ⌈wideScale t⌉₊)
    (by exact Nat.lt_succ_self _) (wideOrder_succ_le_ceil hL)
  exact lt_of_not_ge hnot

/-! ### The strip half-width -/

/-- **The wide strip is at least `5(log L)²/L` wide.** -/
theorem wideEta_ge {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    5 * Real.log (wideScale t) ^ (2 : ℕ) / wideScale t ≤ wideEta t := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ wideOrder t := by positivity
  have h := two_pow_wideOrder_le hL
  rw [wideEta, div_le_div_iff₀ hL0 (by positivity : (0:ℝ) < 6 * (2 : ℝ) ^ wideOrder t)]
  nlinarith

/-- **The wide strip is at most `10(log L)²/L` wide.** -/
theorem wideEta_le {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    wideEta t ≤ 10 * Real.log (wideScale t) ^ (2 : ℕ) / wideScale t := by
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ wideOrder t := by positivity
  have h := lt_two_pow_wideOrder_succ hL
  have hpow : (2 : ℝ) ^ (wideOrder t + 1) = 2 * (2 : ℝ) ^ wideOrder t := by ring
  rw [hpow] at h
  have hlogpos : (0 : ℝ) < Real.log (wideScale t) ^ (2 : ℕ) := by
    have := one_le_log_wideScale_sq hL; linarith
  rw [wideEta, div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * (2 : ℝ) ^ wideOrder t) hL0]
  nlinarith

/-! ### The largeness condition -/

/-- `K³ < 2^K` for `K ≥ 10`. -/
theorem cube_lt_two_pow {K : ℕ} (hK : 10 ≤ K) : (K : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ K := by
  induction K with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 10 with hn | hn
    · have hn10 : n + 1 = 10 := by omega
      rw [hn10]
      norm_num
    · have hprev := ih (by omega)
      have hnR : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by linarith
      have hq : (0 : ℝ) ≤ ((n : ℝ) - 10) * (n : ℝ) := by nlinarith
      have hc : (0 : ℝ) ≤ ((n : ℝ) - 10) * (n : ℝ) ^ (2 : ℕ) := by nlinarith
      have hstep : ((n : ℝ) + 1) ^ (3 : ℕ) ≤ 2 * (n : ℝ) ^ (3 : ℕ) := by nlinarith [hq, hc]
      have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, hpow]
      nlinarith

/-- **The wide order clears the largeness condition.** -/
theorem largenessBound_wideOrder_lt {t : ℝ} (hL : (10 : ℝ) ^ (12 : ℕ) ≤ wideScale t) :
    largenessBound (wideOrder t) < wideScale t := by
  set K : ℕ := wideOrder t with hKdef
  have hK10 : 10 ≤ K := ten_le_wideOrder hL
  have hKR : (10 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK10
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogK : Real.log ((K : ℝ) - 1) ≤ (K : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (K : ℝ) - 1 by linarith)
    linarith
  have hlogKnn : (0 : ℝ) ≤ Real.log ((K : ℝ) - 1) :=
    Real.log_nonneg (by linarith)
  have hA : (0 : ℝ) ≤ ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) := by nlinarith
  have hbound : largenessBound K ≤ (K : ℝ) ^ (3 : ℕ) + (K : ℝ) := by
    rw [largenessBound]
    have h1 : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
        ≤ ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * ((K : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlogK hA
    have h2 : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * ((K : ℝ) - 1) ≤ (K : ℝ) ^ (3 : ℕ) := by
      nlinarith [hKR]
    nlinarith
  have hcube := cube_lt_two_pow hK10
  have hpow := two_pow_wideOrder_le_scale hL
  rw [← hKdef] at hpow
  have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ (2 : ℕ) := by nlinarith
  have hKle : (K : ℝ) ≤ (K : ℝ) ^ (3 : ℕ) := by nlinarith
  have hL0 : (0 : ℝ) < wideScale t := by nlinarith
  nlinarith

end RHTower.Sieve
