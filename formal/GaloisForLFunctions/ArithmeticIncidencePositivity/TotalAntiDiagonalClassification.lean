import GaloisForLFunctions.ArithmeticIncidencePositivity.LatticeCrossingClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomVersusPoleClassification

/-!
# The pole against the whole negative conductance of an anti-diagonal

On the anti-diagonal of `n`, `|x| + y = log n`, the negative conductance per unit gauge is the
archimedean density `ω(log n) = n²/((n² − 1)√n)` plus the atom `Λ(n)/√n`; the pole offers the polar
weight `P(a) = sinh(a/2) sinh((log n − a)/2)`, largest at the midpoint, where it equals
`(√n − 1)²/(4√n)`. The **total anti-diagonal kernel** `ω(log n) + Λ(n)/√n − P(a)` is positive
everywhere iff it is positive at the midpoint, that is iff

    (√n − 1)² < 4n²/(n² − 1) + 4Λ(n).

**Classification.** For `n ≥ 2` this holds iff `n ∈ {2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17, 19, 23}`:
every modulus up to `9`, where the archimedean density alone is unpaid everywhere, and the primes
from `11` to `23`. For every other `n` the pole pays the whole negative conductance at the midpoint.
The last prime is `23`: `(√23 − 1)² < 14.5` against `4·529/528 + 4 log 23 > 16.3`; for `29` the left
side exceeds `19.2` while the right side is below `17.5`. For `x ≥ 30` the inequality
`4x²/(x² − 1) + 4 log x ≤ (√x − 1)²` follows from `log r ≤ sinh(log r)` on the fourth root `r`.
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

/-- `ω(log n) = n² / ((n² − 1) √n)` for `n ≥ 2`. -/
theorem archLevyDensity_log_nat {n : ℕ} (hn : 2 ≤ n) :
    archLevyDensity (Real.log n) = (n : ℝ) ^ 2 / (((n : ℝ) ^ 2 - 1) * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0.le]; ring
  rw [hlog, archLevyDensity_two_mul_log hs]
  have h4 : Real.sqrt n ^ 4 = (n : ℝ) ^ 2 := by
    rw [show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring, Real.sq_sqrt hn0.le]
  rw [h4]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hn2' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have e : 1 - ((n : ℝ) ^ 2)⁻¹ = ((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2 := by
    rw [eq_div_iff hn2'.ne', sub_mul, one_mul, inv_mul_cancel₀ hn2'.ne']
  rw [e, div_div_eq_mul_div, div_eq_div_iff hn2.ne' (by positivity)]
  field_simp

/-- Midpoint value of the total kernel in closed form. -/
theorem totalAntiDiagonalKernel_midpoint_eq {n : ℕ} (hn : 2 ≤ n) :
    totalAntiDiagonalKernel n (Real.log n / 2) =
      (4 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 4 * ArithmeticFunction.vonMangoldt n
        - (Real.sqrt n - 1) ^ 2) / (4 * Real.sqrt n) := by
  unfold totalAntiDiagonalKernel vonMangoldtAtom
  rw [if_pos hn, crossingPolarWeight_midpoint, sinh_log_div_four_sq (by omega),
    archLevyDensity_log_nat hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  field_simp

/-- At the midpoint the total kernel is positive iff `(√n − 1)² < 4n²/(n² − 1) + 4Λ(n)`. -/
theorem totalAntiDiagonalKernel_midpoint_pos_iff {n : ℕ} (hn : 2 ≤ n) :
    0 < totalAntiDiagonalKernel n (Real.log n / 2) ↔
      (Real.sqrt n - 1) ^ 2 <
        4 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 4 * ArithmeticFunction.vonMangoldt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [totalAntiDiagonalKernel_midpoint_eq hn,
    div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * Real.sqrt n), sub_pos]

/-- The midpoint minimizes the total kernel along the anti-diagonal. -/
theorem totalAntiDiagonalKernel_midpoint_le (n : ℕ) (a : ℝ) :
    totalAntiDiagonalKernel n (Real.log n / 2) ≤ totalAntiDiagonalKernel n a := by
  unfold totalAntiDiagonalKernel
  have := crossingPolarWeight_le_midpoint (Real.log n) a
  rw [← crossingPolarWeight_midpoint] at this
  linarith

/-! ### Two bounds on `4x²/(x² − 1)` -/

theorem four_sq_div_gt_four {x : ℝ} (hx : 1 < x) : 4 < 4 * x ^ 2 / (x ^ 2 - 1) := by
  have h : 0 < x ^ 2 - 1 := by nlinarith
  rw [lt_div_iff₀ h]; nlinarith

theorem four_sq_div_le {x m : ℝ} (hm : 1 < m) (hx : m ≤ x) :
    4 * x ^ 2 / (x ^ 2 - 1) ≤ 4 + 4 / (m ^ 2 - 1) := by
  have hm2 : 0 < m ^ 2 - 1 := by nlinarith
  have hx2 : m ^ 2 - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hpos : 0 < x ^ 2 - 1 := lt_of_lt_of_le hm2 hx2
  rw [div_le_iff₀ hpos]
  have h4 : 4 ≤ 4 / (m ^ 2 - 1) * (x ^ 2 - 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm2]; nlinarith
  nlinarith

/-- The polynomial inequality behind the large-prime regime: for `t ≥ 0` and `r = 2.34 + t`,
`4.005 r + 8(r² − 1) ≤ (r² − 1)² r`. -/
theorem large_prime_poly_aux {t : ℝ} (ht : 0 ≤ t) :
    4.005 * (2.34 + t) + 8 * ((2.34 + t) ^ 2 - 1) ≤ ((2.34 + t) ^ 2 - 1) ^ 2 * (2.34 + t) := by
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, ht]

/-- For real `x ≥ 30`, `4x²/(x² − 1) + 4 log x ≤ (√x − 1)²`. -/
theorem four_sq_div_add_four_log_le {x : ℝ} (hx : 30 ≤ x) :
    4 * x ^ 2 / (x ^ 2 - 1) + 4 * Real.log x ≤ (Real.sqrt x - 1) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hfrac : 4 * x ^ 2 / (x ^ 2 - 1) ≤ 4.005 := by
    have := four_sq_div_le (by norm_num : (1 : ℝ) < 30) hx
    norm_num at this ⊢
    linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt x) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.mpr hsx
  have hr2 : r ^ 2 = Real.sqrt x := by rw [hr_def]; exact Real.sq_sqrt hsx.le
  have hr4 : r ^ 4 = x := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hx0.le]
  have hr234 : (2.34 : ℝ) ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h4 : r ^ 4 < (2.34 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr.le (by norm_num)
    rw [hr4] at h4
    norm_num at h4
    linarith
  have hr1 : 1 < r := by linarith
  have hlog : Real.log x = 4 * Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  have hsinh : Real.log r ≤ (r - r⁻¹) / 2 := by
    have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr1.le)
    rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log hr] at h
  have h2 : 8 * (r ^ 2 - 1) / r = 8 * (r - r⁻¹) := by
    rw [mul_div_assoc, sub_div, pow_two, mul_div_assoc, div_self hr.ne', mul_one, one_div]
  have hsq : (Real.sqrt x - 1) ^ 2 = (r ^ 2 - 1) ^ 2 := by rw [hr2]
  rw [hsq, hlog]
  have key := large_prime_poly_aux (t := r - 2.34) (by linarith)
  rw [show (2.34 : ℝ) + (r - 2.34) = r by ring] at key
  have h3 : 8 * (r ^ 2 - 1) / r ≤ (r ^ 2 - 1) ^ 2 - 4.005 := by
    rw [div_le_iff₀ hr]; nlinarith
  linarith

/-! ### The classification -/

/-- The thirteen moduli on whose anti-diagonal the pole pays the negative conductance nowhere. -/
def totalDominatedModuli : Finset ℕ := {2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17, 19, 23}

/-- **Classification.** For `n ≥ 2`, `(√n − 1)² < 4n²/(n² − 1) + 4Λ(n)` iff
`n ∈ {2, …, 9, 11, 13, 17, 19, 23}`. -/
theorem total_midpoint_inequality_iff {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt n - 1) ^ 2 <
        4 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + 4 * ArithmeticFunction.vonMangoldt n ↔
      n ∈ totalDominatedModuli := by
  simp only [totalDominatedModuli, Finset.mem_insert, Finset.mem_singleton]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hfrac := four_sq_div_gt_four hn1
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rcases Nat.lt_or_ge n 10 with h10 | h10
  · -- `n ≤ 9`: `(√n − 1)² ≤ 4 < 4n²/(n² − 1)`
    refine iff_of_true ?_ (by interval_cases n <;> norm_num)
    have hs3 : Real.sqrt n ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ 9))
    have hs1 : 1 ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
    have h4 : (Real.sqrt n - 1) * (Real.sqrt n - 1) ≤ 2 * 2 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    nlinarith
  · -- `n ≥ 10`
    have h10r : (10 : ℝ) ≤ n := by exact_mod_cast h10
    have hfrac_le := four_sq_div_le (by norm_num : (1 : ℝ) < 10) h10r
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hp2 := hp.two_le
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · -- `n = p` prime, `p ≥ 11`
        obtain rfl : k = 1 := by omega
        simp only [pow_one] at h10 h10r hfrac hfrac_le hn1 ⊢
        constructor
        · intro h
          rcases Nat.lt_or_ge p 29 with h29 | h29
          · interval_cases p <;> (revert hp; norm_num)
          · exfalso
            rcases Nat.lt_or_ge p 30 with h30 | h30
            · obtain rfl : p = 29 := by omega
              push_cast at h
              rw [sqrt_sub_one_sq_eq (by norm_num)] at h
              have hU : Real.sqrt 29 < (5.386 : ℝ) :=
                (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
              have h32 : Real.log (29 : ℝ) ≤ 5 * Real.log 2 + (29 / 32 - 1) := by
                have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 29 / 32)
                rw [Real.log_div (by norm_num) (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num,
                  Real.log_pow] at hh
                push_cast at hh
                linarith
              have := Real.log_two_lt_d9
              have hf : 4 * (29 : ℝ) ^ 2 / ((29 : ℝ) ^ 2 - 1) = 3364 / 840 := by norm_num
              rw [hf] at h
              linarith
            · have := four_sq_div_add_four_log_le (x := (p : ℝ)) (by exact_mod_cast h30)
              linarith
        · intro h
          rcases Nat.lt_or_ge p 20 with h20 | h20
          · have := sqrt_sub_one_sq_lt_four_log_of_prime_le_nineteen hp (by omega)
            linarith
          · obtain rfl : p = 23 := by omega
            push_cast at hfrac ⊢
            have hL : (4.79 : ℝ) < Real.sqrt 23 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
            have hlog := log_add_one_sub_div_le_log (m := 16) (p := 23) (by norm_num) (by norm_num)
            rw [log_sixteen_eq] at hlog
            have := Real.log_two_gt_d9
            exact sqrt_sub_one_sq_lt (by norm_num) hL (by linarith)
      · -- `n = p^k`, `k ≥ 2`, `n ≥ 10`: never dominated
        refine iff_of_false ?_ ?_
        · rw [not_lt]
          rcases Nat.lt_or_ge p 5 with hp5 | hp5
          · interval_cases p
            · -- `p = 2`, `k ≥ 4`
              have hk4 : 4 ≤ k := by
                rcases Nat.lt_or_ge k 4 with hlt | hge
                · interval_cases k <;> norm_num at h10
                · exact hge
              have h16 : (16 : ℕ) ≤ 2 ^ k := by
                calc (16 : ℕ) = 2 ^ 4 := by norm_num
                  _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
              have h16r : (16 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h16
              have hs : (4 : ℝ) ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
                rw [show (4 : ℝ) = Real.sqrt 16 by
                  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
                exact Real.sqrt_le_sqrt h16r
              have hfl := four_sq_div_le (by norm_num : (1 : ℝ) < 16) h16r
              have h9 : (3 : ℝ) ^ 2 ≤ (Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by linarith) 2
              have := Real.log_two_lt_d9
              simp only [Nat.cast_ofNat]
              have c1 : (4 : ℝ) + 4 / (16 ^ 2 - 1) = 1024 / 255 := by norm_num
              have c2 : (3 : ℝ) ^ 2 = 9 := by norm_num
              linarith
            · -- `p = 3`, `k ≥ 3`
              have hk3 : 3 ≤ k := by
                rcases Nat.lt_or_ge k 3 with hlt | hge
                · interval_cases k; norm_num at h10
                · exact hge
              have h27 : (27 : ℕ) ≤ 3 ^ k := by
                calc (27 : ℕ) = 3 ^ 3 := by norm_num
                  _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
              have h27r : (27 : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast h27
              have hs : (5 : ℝ) ≤ Real.sqrt ((3 ^ k : ℕ) : ℝ) := by
                rw [show (5 : ℝ) = Real.sqrt 25 by
                  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
                exact Real.sqrt_le_sqrt (by linarith)
              have hfl := four_sq_div_le (by norm_num : (1 : ℝ) < 27) h27r
              have h16 : (4 : ℝ) ^ 2 ≤ (Real.sqrt ((3 ^ k : ℕ) : ℝ) - 1) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by linarith) 2
              have hlog : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
              simp only [Nat.cast_ofNat]
              have c1 : (4 : ℝ) + 4 / (27 ^ 2 - 1) = 2916 / 728 := by norm_num
              have c2 : (4 : ℝ) ^ 2 = 16 := by norm_num
              linarith
            · -- `4` is not prime
              norm_num at hp
          · -- `p ≥ 5`, `k ≥ 2`: `n ≥ 25`, `(√n − 1)² ≥ (p − 1)²`
            have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
            have hpk : (p : ℝ) ^ 2 ≤ ((p ^ k : ℕ) : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right hp.pos hk2
            have h25 : (25 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by nlinarith
            have hs : (p : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) :=
              (Real.le_sqrt (by linarith) (by linarith)).mpr hpk
            have hfl := four_sq_div_le (by norm_num : (1 : ℝ) < 25) h25
            have hC : ((p : ℝ) - 1) ^ 2 ≤ (Real.sqrt ((p ^ k : ℕ) : ℝ) - 1) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (by linarith) 2
            have hL : Real.log p ≤ 3 * Real.log 2 + ((p : ℝ) / 8 - 1) := by
              have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (p : ℝ) / 8)
              rw [Real.log_div (by linarith) (by norm_num), log_eight_eq] at h
              linarith
            have := Real.log_two_lt_d9
            have c1 : (4 : ℝ) + 4 / (25 ^ 2 - 1) = 625 / 156 := by norm_num
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 5)
              (by linarith : (0 : ℝ) ≤ (p : ℝ) + 5 / 2)]
        · -- `p^k` with `k ≥ 2` is none of the thirteen moduli
          rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
          all_goals first
            | omega
            | (obtain ⟨-, hk1⟩ := (Nat.Prime.pow_eq_iff (by norm_num)).mp h; omega)
    · -- not a prime power, `n ≥ 10`: `(√n − 1)² ≥ (√10 − 1)² > 4n²/(n² − 1)`
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      refine iff_of_false ?_ ?_
      · rw [not_lt, mul_zero, add_zero]
        have hs : Real.sqrt 10 ≤ Real.sqrt n := Real.sqrt_le_sqrt h10r
        have hL : (3.16 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
        have h2 : (2.16 : ℝ) ^ 2 ≤ (Real.sqrt n - 1) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 2
        norm_num at hfrac_le h2
        linarith
      · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> subst h
        all_goals first
          | omega
          | exact hpp (Nat.Prime.isPrimePow (by norm_num))

/-- **Midpoint law.** The total kernel is positive at the midpoint iff `n` is one of the thirteen. -/
theorem totalAntiDiagonalKernel_midpoint_pos_iff_mem {n : ℕ} (hn : 2 ≤ n) :
    0 < totalAntiDiagonalKernel n (Real.log n / 2) ↔ n ∈ totalDominatedModuli := by
  rw [totalAntiDiagonalKernel_midpoint_pos_iff hn, total_midpoint_inequality_iff hn]

/-- **Anti-diagonal law.** The pole pays the negative conductance of the anti-diagonal of `n`
nowhere iff `n ∈ {2, …, 9, 11, 13, 17, 19, 23}`. -/
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

end GaloisForLFunctions.ArithmeticIncidencePositivity
