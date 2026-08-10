import GaloisForLFunctions.RHTower.Sieve.GhsHeightWindow

/-!
# A height inside the window

The window `(log N)³ ≪ n ≪ N^{1/4}` is non-empty for large `N`, and

```text
ghsHeight N := ⌊(log N)⁶⌋ + 1
```

lies in it.  Its lower bound `(log N)⁶ ≤ ghsHeight N` clears the height inequality — in fact with an
enormous margin, `10/9` against `1750·ghsShapeConst ≥ 15750`, so that condition needs no
asymptotics at all.  Its upper bound `ghsHeight N ≤ 2(log N)⁶` meets `n² ≤ ghsScale N 1` through the
one genuinely asymptotic comparison of the whole construction,

```text
4(log N)¹² ≤ ⌊N^{1/2}⌋   eventually,
```

which is `log =o(x^{1/24})` raised to the twelfth power.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset

/-- **The eighth power of the logarithm is below the square-root scale.** -/
theorem eventually_pow_log_le_ghsScale :
    ∀ᶠ N : ℕ in Filter.atTop, 4 * (Real.log N) ^ 12 ≤ ((ghsScale N 1 : ℕ) : ℝ) := by
  have hlo : (fun x : ℝ => Real.log x) =o[Filter.atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 24)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hpow := hlo.pow (n := 12) (by norm_num)
  have hdef := hpow.def (show (0 : ℝ) < 1 / 8 by norm_num)
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      4 * (Real.log x) ^ 12 ≤ (1 / 2) * x ^ ((1 : ℝ) / 2) := by
    filter_upwards [hdef, Filter.eventually_ge_atTop (4 : ℝ)] with x hx hx4
    have hx0 : (0 : ℝ) < x := by linarith
    have hrw : (x ^ ((1 : ℝ) / 24)) ^ 12 = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 24)) 12, ← Real.rpow_mul hx0.le]
      norm_num
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hrw,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log x) ^ 12),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    linarith
  have hnat : ∀ᶠ N : ℕ in Filter.atTop,
      4 * (Real.log N) ^ 12 ≤ (1 / 2) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop 16] with N hN hN16
  have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have h16 : ((16 : ℝ)) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) hN16R (by norm_num)
    have heq : ((16 : ℝ)) ^ ((1 : ℝ) / 2) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 2,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [h16, heq.le, heq.ge]
  have hs : ghsScale N 1 = ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ := by norm_num [ghsScale]
  have hfl : (N : ℝ) ^ ((1 : ℝ) / 2) - 1 < ((⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / 2))]
  rw [hs]
  linarith [hN, h4, hfl]

/-- The height the argument uses. -/
def ghsHeight (N : ℕ) : ℕ := ⌊(Real.log N) ^ 6⌋₊ + 1

theorem log_pow_le_ghsHeight (N : ℕ) : (Real.log N) ^ 6 ≤ ((ghsHeight N : ℕ) : ℝ) := by
  rw [ghsHeight]
  push_cast
  linarith [Nat.lt_floor_add_one ((Real.log N) ^ 6)]

theorem ghsHeight_le {N : ℕ} (h : (1 : ℝ) ≤ (Real.log N) ^ 6) :
    ((ghsHeight N : ℕ) : ℝ) ≤ 2 * (Real.log N) ^ 6 := by
  rw [ghsHeight]
  push_cast
  have := Nat.floor_le (le_trans zero_le_one h)
  linarith

/-- **The height inequality, with an enormous margin and no asymptotics.** -/
theorem ghs_height_inequality {N n : ℕ} (hlogN : (3 : ℝ) ≤ Real.log N)
    (hn : (Real.log N) ^ 4 ≤ (n : ℝ)) :
    (5 / (4 * (n : ℝ)))
        * ((16 / 9) * (Real.log N / (4 * Real.log 2)) ^ 2 * (Real.log N + Real.log 4))
      ≤ 1750 * ghsShapeConst := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set L : ℝ := Real.log N with hLdef
  have hL : (3 : ℝ) ≤ L := hlogN
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq9 : (9 : ℝ) ≤ L ^ 2 := by nlinarith [hL]
  have h81 : (81 : ℝ) ≤ L ^ 4 := by nlinarith [hsq9, sq_nonneg (L ^ 2 - 9)]
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith [hn, h81]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog4le : Real.log 4 ≤ L := by rw [hlog4]; linarith
  have hlog40 : (0 : ℝ) ≤ Real.log 4 := by rw [hlog4]; linarith
  have hden : (2 : ℝ) ≤ 4 * Real.log 2 := by linarith
  have hden4 : (4 : ℝ) ≤ (4 * Real.log 2) ^ 2 := by nlinarith [hden]
  have hsq : (L / (4 * Real.log 2)) ^ 2 ≤ L ^ 2 / 4 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sq_nonneg L) (by linarith [hden4] :
      (0 : ℝ) ≤ (4 * Real.log 2) ^ 2 - 4)]
  have hstep : (16 / 9 : ℝ) * (L / (4 * Real.log 2)) ^ 2 * (L + Real.log 4)
      ≤ (16 / 9) * (L ^ 2 / 4) * (2 * L) := by
    have hs0 : (0 : ℝ) ≤ L + Real.log 4 := by linarith
    have h2 : L + Real.log 4 ≤ 2 * L := by linarith
    have hq0 : (0 : ℝ) ≤ (L / (4 * Real.log 2)) ^ 2 := sq_nonneg _
    have hA : (16 / 9 : ℝ) * (L / (4 * Real.log 2)) ^ 2 * (L + Real.log 4)
        ≤ (16 / 9) * (L ^ 2 / 4) * (L + Real.log 4) := by
      have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 16 / 9)
      nlinarith [this, hs0]
    have hB : (16 / 9 : ℝ) * (L ^ 2 / 4) * (L + Real.log 4)
        ≤ (16 / 9) * (L ^ 2 / 4) * (2 * L) := by
      have hc : (0 : ℝ) ≤ (16 / 9 : ℝ) * (L ^ 2 / 4) := by positivity
      exact mul_le_mul_of_nonneg_left h2 hc
    linarith [hA, hB]
  have hcoef : (0 : ℝ) ≤ 5 / (4 * (n : ℝ)) := by positivity
  have hmain : (5 / (4 * (n : ℝ))) * ((16 / 9) * (L ^ 2 / 4) * (2 * L)) ≤ 10 / 9 := by
    have hkey : (5 / (4 * (n : ℝ))) * ((16 / 9) * (L ^ 2 / 4) * (2 * L))
        = (10 / 9) * (L ^ 3 / (n : ℝ)) := by
      field_simp; ring
    rw [hkey]
    have hratio : L ^ 3 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      nlinarith [hn, hL, pow_nonneg hL0.le 3]
    linarith [hratio]
  have hΓ : (9 : ℝ) ≤ ghsShapeConst := by
    rw [ghsShapeConst]
    have hC := mertensBlockGapConst_nonneg
    nlinarith [hlog40]
  linarith [mul_le_mul_of_nonneg_left hstep hcoef, hmain, hΓ]

end RHTower.Sieve

end
