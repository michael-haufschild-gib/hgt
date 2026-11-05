import GaloisForLFunctions.ArithmeticIncidencePositivity.LatticeCrossingClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomVersusPoleClassification

/-!
# The pole against the whole negative conductance of an anti-diagonal

On the anti-diagonal of `n`, `|x| + y = log n`, the negative conductance per unit gauge is the
archimedean density `ω(log n) = n²/((n² − 1)√n)` plus the atom `Λ(n)/√n`; the pole offers the polar
weight `P(a) = 2 sinh(a/2) sinh((log n − a)/2)`, largest at the midpoint, where it equals
`cosh(log n / 2) − 1 = (√n − 1)²/(2√n)`. The **total anti-diagonal kernel** `ω(log n) + Λ(n)/√n − P(a)`
is positive everywhere iff it is positive at the midpoint, that is iff

    (√n − 1)² < 2n²/(n² − 1) + 2Λ(n).

**Classification.** For `n ≥ 2` this holds iff `n ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13}`: the moduli up to
`5`, where the archimedean density alone is unpaid everywhere, the prime powers `7, 8, 9`, and the
primes `11`, `13`. For every other `n` the pole pays the whole negative conductance at the midpoint;
`6` is the first such modulus (`(√6 − 1)² > 2.09` against `72/35 < 2.06`) and `17` the first such
prime. The near misses are `8` (`3.344` against `3.418`) and `9` (`4` against `4.07`). For `x ≥ 17`
the inequality `2x²/(x² − 1) + 2 log x ≤ (√x − 1)²` follows from `log r ≤ sinh(log r)` on the
fourth root `r`.
-/

open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The total anti-diagonal kernel of `n` at the point `(−a, log n − a)`: archimedean density plus
atom minus polar weight. -/
def totalAntiDiagonalKernel (n : ℕ) (a : ℝ) : ℝ :=
  archLevyDensity (Real.log n) + vonMangoldtAtom n - crossingPolarWeight (Real.log n) a

theorem totalAntiDiagonalKernel_eq {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    totalAntiDiagonalKernel n a = archPairKernel (-a) (Real.log n - a) + vonMangoldtAtom n := by
  unfold totalAntiDiagonalKernel
  rw [archPairKernel_antiDiagonal_eq (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))]
  ring

/-- Midpoint value of the total kernel in closed form. -/
theorem totalAntiDiagonalKernel_midpoint_eq {n : ℕ} (hn : 2 ≤ n) :
    totalAntiDiagonalKernel n (Real.log n / 2) =
      (2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 2 * ArithmeticFunction.vonMangoldt n
        - (Real.sqrt n - 1) ^ 2) / (2 * Real.sqrt n) := by
  unfold totalAntiDiagonalKernel vonMangoldtAtom
  rw [if_pos hn, crossingPolarWeight_midpoint, sinh_log_div_four_sq (by omega),
    archLevyDensity_log_nat hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  field_simp
  ring

/-- At the midpoint the total kernel is positive iff `(√n − 1)² < 2n²/(n² − 1) + 2Λ(n)`. -/
theorem totalAntiDiagonalKernel_midpoint_pos_iff {n : ℕ} (hn : 2 ≤ n) :
    0 < totalAntiDiagonalKernel n (Real.log n / 2) ↔
      (Real.sqrt n - 1) ^ 2 <
        2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 2 * ArithmeticFunction.vonMangoldt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [totalAntiDiagonalKernel_midpoint_eq hn,
    div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * Real.sqrt n), sub_pos]

/-- The midpoint minimizes the total kernel along the anti-diagonal. -/
theorem totalAntiDiagonalKernel_midpoint_le (n : ℕ) (a : ℝ) :
    totalAntiDiagonalKernel n (Real.log n / 2) ≤ totalAntiDiagonalKernel n a := by
  unfold totalAntiDiagonalKernel
  have := crossingPolarWeight_le_midpoint (Real.log n) a
  rw [← crossingPolarWeight_midpoint] at this
  linarith

/-! ### Two bounds on `2x²/(x² − 1)` -/

theorem two_sq_div_gt_two {x : ℝ} (hx : 1 < x) : 2 < 2 * x ^ 2 / (x ^ 2 - 1) := by
  have h : 0 < x ^ 2 - 1 := by nlinarith
  rw [lt_div_iff₀ h]; nlinarith

theorem two_sq_div_le {x m : ℝ} (hm : 1 < m) (hx : m ≤ x) :
    2 * x ^ 2 / (x ^ 2 - 1) ≤ 2 + 2 / (m ^ 2 - 1) := by
  have hm2 : 0 < m ^ 2 - 1 := by nlinarith
  have hx2 : m ^ 2 - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hpos : 0 < x ^ 2 - 1 := lt_of_lt_of_le hm2 hx2
  rw [div_le_iff₀ hpos]
  have h2 : 2 ≤ 2 / (m ^ 2 - 1) * (x ^ 2 - 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm2]; nlinarith
  nlinarith

/-- The polynomial inequality behind the large-prime regime: for `t ≥ 0` and `r = 2.03 + t`,
`2.007 r + 4(r² − 1) ≤ (r² − 1)² r`. -/
theorem large_prime_poly_aux {t : ℝ} (ht : 0 ≤ t) :
    2.007 * (2.03 + t) + 4 * ((2.03 + t) ^ 2 - 1) ≤ ((2.03 + t) ^ 2 - 1) ^ 2 * (2.03 + t) := by
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, ht]

/-- For real `x ≥ 17`, `2x²/(x² − 1) + 2 log x ≤ (√x − 1)²`. -/
theorem two_sq_div_add_two_log_le {x : ℝ} (hx : 17 ≤ x) :
    2 * x ^ 2 / (x ^ 2 - 1) + 2 * Real.log x ≤ (Real.sqrt x - 1) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hfrac : 2 * x ^ 2 / (x ^ 2 - 1) ≤ 2.007 := by
    have := two_sq_div_le (by norm_num : (1 : ℝ) < 17) hx
    norm_num at this ⊢
    linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt x) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.mpr hsx
  have hr2 : r ^ 2 = Real.sqrt x := by rw [hr_def]; exact Real.sq_sqrt hsx.le
  have hr4 : r ^ 4 = x := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hx0.le]
  have hr203 : (2.03 : ℝ) ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h4 : r ^ 4 < (2.03 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr.le (by norm_num)
    rw [hr4] at h4
    norm_num at h4
    linarith
  have hr1 : 1 < r := by linarith
  have hlog : Real.log x = 4 * Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  have hsinh : Real.log r ≤ (r - r⁻¹) / 2 := by
    have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr1.le)
    rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log hr] at h
  have h2 : 4 * (r ^ 2 - 1) / r = 4 * (r - r⁻¹) := by
    rw [mul_div_assoc, sub_div, pow_two, mul_div_assoc, div_self hr.ne', mul_one, one_div]
  have hsq : (Real.sqrt x - 1) ^ 2 = (r ^ 2 - 1) ^ 2 := by rw [hr2]
  rw [hsq, hlog]
  have key := large_prime_poly_aux (t := r - 2.03) (by linarith)
  rw [show (2.03 : ℝ) + (r - 2.03) = r by ring] at key
  have h3 : 4 * (r ^ 2 - 1) / r ≤ (r ^ 2 - 1) ^ 2 - 2.007 := by
    rw [div_le_iff₀ hr]; nlinarith
  linarith

/-! ### The classification -/

/-- The nine moduli on whose anti-diagonal the pole pays the negative conductance nowhere. -/
def totalDominatedModuli : Finset ℕ := {2, 3, 4, 5, 7, 8, 9, 11, 13}

/-- **Classification.** For `n ≥ 2`, `(√n − 1)² < 2n²/(n² − 1) + 2Λ(n)` iff
`n ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13}`. -/
theorem total_midpoint_inequality_iff {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt n - 1) ^ 2 <
        2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 2 * ArithmeticFunction.vonMangoldt n ↔
      n ∈ totalDominatedModuli := by
  simp only [totalDominatedModuli, Finset.mem_insert, Finset.mem_singleton]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hfrac := two_sq_div_gt_two hn1
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hl2 := Real.log_two_gt_d9
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · -- `n ≤ 5`: `(√n − 1)² < 2 < 2n²/(n² − 1)`
    refine iff_of_true ?_ (by interval_cases n <;> norm_num)
    have hs5 : Real.sqrt n < 2.24 := by
      calc Real.sqrt n ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ 5))
        _ < 2.24 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hs1 : 1 ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
    have h4 : (Real.sqrt n - 1) * (Real.sqrt n - 1) ≤ 1.24 * 1.24 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    nlinarith
  · -- `n ≥ 6`
    have h6r : (6 : ℝ) ≤ n := by exact_mod_cast h6
    have hfrac_le := two_sq_div_le (by norm_num : (1 : ℝ) < 6) h6r
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hp2 := hp.two_le
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · -- `n = p` prime, `p ≥ 7`
        obtain rfl : k = 1 := by omega
        simp only [pow_one] at h6 h6r hfrac hfrac_le hn1 ⊢
        constructor
        · intro h
          rcases Nat.lt_or_ge p 17 with h17 | h17
          · interval_cases p <;> (revert hp; norm_num)
          · exfalso
            have := two_sq_div_add_two_log_le (x := (p : ℝ)) (by exact_mod_cast h17)
            linarith
        · intro h
          have hcases : p = 7 ∨ p = 11 ∨ p = 13 := by
            rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | omega | (norm_num at hp)
          rcases hcases with rfl | rfl | rfl
          · push_cast at hfrac ⊢
            have hL : (2.64 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            have hlog := log_add_one_sub_div_le_log (m := 4) (p := 7) (by norm_num) (by norm_num)
            rw [log_four_eq] at hlog
            exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
          · push_cast at hfrac ⊢
            have hL : (3.31 : ℝ) < Real.sqrt 11 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            have hlog := log_add_one_sub_div_le_log (m := 8) (p := 11) (by norm_num) (by norm_num)
            rw [log_eight_eq] at hlog
            exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
          · push_cast at hfrac ⊢
            have hL : (3.6 : ℝ) < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            have hlog := log_add_one_sub_div_le_log (m := 8) (p := 13) (by norm_num) (by norm_num)
            rw [log_eight_eq] at hlog
            exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
      · -- `n = p^k`, `k ≥ 2`, `n ≥ 6`: dominated exactly for `8` and `9`
        rcases Nat.lt_or_ge p 5 with hp5 | hp5
        · interval_cases p
          · -- `p = 2`, `k ≥ 3`
            have hk3 : 3 ≤ k := by
              rcases Nat.lt_or_ge k 3 with hlt | hge
              · interval_cases k; norm_num at h6
              · exact hge
            rcases Nat.lt_or_ge k 4 with hk4 | hk4
            · -- `n = 8`: `9 − 2√8 < 128/63 + 2 log 2`
              obtain rfl : k = 3 := by omega
              refine iff_of_true ?_ (by norm_num)
              push_cast
              have hL : (2.8284 : ℝ) < Real.sqrt 8 :=
                (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
              have hf : 2 * (8 : ℝ) ^ 2 / ((8 : ℝ) ^ 2 - 1) = 128 / 63 := by norm_num
              rw [hf]
              exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
            · -- `n ≥ 16`
              refine iff_of_false ?_ ?_
              · rw [not_lt]
                have h16 : (16 : ℕ) ≤ 2 ^ k := by
                  calc (16 : ℕ) = 2 ^ 4 := by norm_num
                    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
                have h16r : (16 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h16
                have hs : (4 : ℝ) ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
                  rw [show (4 : ℝ) = Real.sqrt 16 by
                    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
                  exact Real.sqrt_le_sqrt h16r
                have hfl := two_sq_div_le (by norm_num : (1 : ℝ) < 16) h16r
                have h9 : (3 : ℝ) ^ 2 ≤ (Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1) ^ 2 :=
                  pow_le_pow_left₀ (by norm_num) (by linarith) 2
                have := Real.log_two_lt_d9
                simp only [Nat.cast_ofNat]
                have c1 : (2 : ℝ) + 2 / (16 ^ 2 - 1) = 512 / 255 := by norm_num
                have c2 : (3 : ℝ) ^ 2 = 9 := by norm_num
                linarith
              · have h16 : (16 : ℕ) ≤ 2 ^ k := by
                  calc (16 : ℕ) = 2 ^ 4 := by norm_num
                    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
                omega
          · -- `p = 3`
            rcases Nat.lt_or_ge k 3 with hk3 | hk3
            · -- `n = 9`: `4 < 162/80 + 2 log 3`
              obtain rfl : k = 2 := by omega
              refine iff_of_true ?_ (by norm_num)
              push_cast
              have h9 : Real.sqrt 9 = 3 := by
                rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
              rw [h9]
              have hlog := log_add_one_sub_div_le_log (m := 2) (p := 3) (by norm_num) (by norm_num)
              norm_num
              linarith
            · -- `n ≥ 27`
              refine iff_of_false ?_ ?_
              · rw [not_lt]
                have h27 : (27 : ℕ) ≤ 3 ^ k := by
                  calc (27 : ℕ) = 3 ^ 3 := by norm_num
                    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
                have h27r : (27 : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast h27
                have hs : (5 : ℝ) ≤ Real.sqrt ((3 ^ k : ℕ) : ℝ) := by
                  rw [show (5 : ℝ) = Real.sqrt 25 by
                    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
                  exact Real.sqrt_le_sqrt (by linarith)
                have hfl := two_sq_div_le (by norm_num : (1 : ℝ) < 27) h27r
                have h16 : (4 : ℝ) ^ 2 ≤ (Real.sqrt ((3 ^ k : ℕ) : ℝ) - 1) ^ 2 :=
                  pow_le_pow_left₀ (by norm_num) (by linarith) 2
                have hlog : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
                simp only [Nat.cast_ofNat]
                have c1 : (2 : ℝ) + 2 / (27 ^ 2 - 1) = 1458 / 728 := by norm_num
                have c2 : (4 : ℝ) ^ 2 = 16 := by norm_num
                linarith
              · have h27 : (27 : ℕ) ≤ 3 ^ k := by
                  calc (27 : ℕ) = 3 ^ 3 := by norm_num
                    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
                omega
          · -- `4` is not prime
            norm_num at hp
        · -- `p ≥ 5`, `k ≥ 2`: `n ≥ 25`, `(√n − 1)² ≥ (p − 1)²`
          refine iff_of_false ?_ ?_
          · rw [not_lt]
            have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
            have hpk : (p : ℝ) ^ 2 ≤ ((p ^ k : ℕ) : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right hp.pos hk2
            have h25 : (25 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by nlinarith
            have hs : (p : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) :=
              (Real.le_sqrt (by linarith) (by linarith)).mpr hpk
            have hfl := two_sq_div_le (by norm_num : (1 : ℝ) < 25) h25
            have hC : ((p : ℝ) - 1) ^ 2 ≤ (Real.sqrt ((p ^ k : ℕ) : ℝ) - 1) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (by linarith) 2
            have hL : Real.log p ≤ (p : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
            have c1 : (2 : ℝ) + 2 / (25 ^ 2 - 1) = 1250 / 624 := by norm_num
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)
              (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3)]
          · have h25 : (25 : ℕ) ≤ p ^ k := by
              calc (25 : ℕ) = 5 ^ 2 := by norm_num
                _ ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
                _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
            omega
    · -- not a prime power, `n ≥ 6`: `(√n − 1)² ≥ (√6 − 1)² > 72/35 ≥ 2n²/(n² − 1)`
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      refine iff_of_false ?_ ?_
      · rw [not_lt, mul_zero, add_zero]
        have hs : Real.sqrt 6 ≤ Real.sqrt n := Real.sqrt_le_sqrt h6r
        have hL : (2.449 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
        have h2 : (1.449 : ℝ) ^ 2 ≤ (Real.sqrt n - 1) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 2
        have c1 : (2 : ℝ) + 2 / (6 ^ 2 - 1) = 72 / 35 := by norm_num
        have c2 : (1.449 : ℝ) ^ 2 = 2.099601 := by norm_num
        linarith
      · rintro (h | h | h | h | h | h | h | h | h) <;> subst h
        · omega
        · omega
        · omega
        · omega
        · exact hpp (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 7))
        · exact hpp ((isPrimePow_nat_iff 8).mpr ⟨2, 3, Nat.prime_two, by norm_num, by norm_num⟩)
        · exact hpp ((isPrimePow_nat_iff 9).mpr ⟨3, 2, Nat.prime_three, by norm_num, by norm_num⟩)
        · exact hpp (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11))
        · exact hpp (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 13))

/-- **Midpoint law.** The total kernel is positive at the midpoint iff `n` is one of the nine. -/
theorem totalAntiDiagonalKernel_midpoint_pos_iff_mem {n : ℕ} (hn : 2 ≤ n) :
    0 < totalAntiDiagonalKernel n (Real.log n / 2) ↔ n ∈ totalDominatedModuli := by
  rw [totalAntiDiagonalKernel_midpoint_pos_iff hn, total_midpoint_inequality_iff hn]

/-- **Anti-diagonal law.** The pole pays the negative conductance of the anti-diagonal of `n`
nowhere iff `n ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13}`. -/
theorem totalAntiDiagonalKernel_pos_forall_iff {n : ℕ} (hn : 2 ≤ n) :
    (∀ a : ℝ, 0 < totalAntiDiagonalKernel n a) ↔ n ∈ totalDominatedModuli := by
  rw [← totalAntiDiagonalKernel_midpoint_pos_iff_mem hn]
  constructor
  · intro h; exact h _
  · intro h a; exact lt_of_lt_of_le h (totalAntiDiagonalKernel_midpoint_le n a)

/-- For every other `n ≥ 2` the pole pays the whole negative conductance at the midpoint. -/
theorem totalAntiDiagonalKernel_midpoint_nonpos {n : ℕ} (hn : 2 ≤ n)
    (h : n ∉ totalDominatedModuli) : totalAntiDiagonalKernel n (Real.log n / 2) ≤ 0 := by
  rw [← not_lt, totalAntiDiagonalKernel_midpoint_pos_iff_mem hn]; exact h

#print axioms total_midpoint_inequality_iff
#print axioms totalAntiDiagonalKernel_pos_forall_iff
#print axioms totalAntiDiagonalKernel_midpoint_nonpos

end GaloisForLFunctions.ArithmeticIncidencePositivity
