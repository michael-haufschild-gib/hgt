import GaloisForLFunctions.RHTower.Sieve.VinogradovLogRatioExplicit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vinogradov's estimate for `Σ n^{it}`

Fix an integer `r ≥ 4` and `P = 2Q ≥ P₀(r)` with `P^{4r} ≤ t ≤ P^{4r+4}`.  For every interval
`(A, A+L] ⊂ [4P⁴, 162P⁴]`,

`‖Σ_{A<n≤A+L} n^{it}‖ ≤ 4 M_r L P^{-δ_r} + 400 P²`

(`norm_sum_logPhase_le_vinogradov`), where

* the degree is `k = 2r + 2`, the number of variables `b = k²(⌊log₂ K⌋ + 1)`, `K = k(k+1)/2`, so the
  mean value defect is `< 1`;
* the useful coordinates are `r + ⌊r/8⌋ + 2 ≤ j+1 ≤ ⌊14r/9⌋`, each saving `P^{⌊r/4⌋}`: the
  Taylor coefficient `α_{j} = t/(2π(j+1)x^{j+1})` then lies in the window
  `[P^{2e - 2(j+1)}, 1/(P^{2e}+1)]` for every `x ∈ [4P⁴, 162P⁴]`;
* `δ_r = (n_r ⌊r/4⌋ - 2)/(4b²)` with `n_r = ⌊14r/9⌋ + 1 - (r + ⌊r/8⌋ + 2)` useful coordinates and
  `M_r = (C_{k,b}² (24b²)^k)^{1/(4b²)}`.

The Taylor remainder costs `2π (t/π)(4P²)^{-(k+1)} Q² ≤ 1/2` per point because
`2(k+1) = 4r + 6`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The degree `k = 2r + 2`. -/
def vinogradovWeylDegree (r : ℕ) : ℕ := 2 * r + 2

/-- `K = k(k+1)/2`. -/
def vinogradovWeylK (r : ℕ) : ℕ := vinogradovWeylDegree r * (vinogradovWeylDegree r + 1) / 2

/-- The number of variables `b = k²(⌊log₂ K⌋ + 1)`. -/
def vinogradovWeylMoment (r : ℕ) : ℕ :=
  vinogradovWeylDegree r ^ 2 * (Nat.log 2 (vinogradovWeylK r) + 1)

/-- Lowest useful power `r + ⌊r/8⌋ + 2`. -/
def vinogradovWeylLow (r : ℕ) : ℕ := r + r / 8 + 2

/-- Highest useful power `⌊14r/9⌋`. -/
def vinogradovWeylHigh (r : ℕ) : ℕ := 14 * r / 9

/-- Saving per useful coordinate `⌊r/4⌋`. -/
def vinogradovWeylSave (r : ℕ) : ℕ := r / 4

/-- The useful coordinates. -/
def vinogradovWeylUseful (r : ℕ) (j : Fin (vinogradovWeylDegree r)) : Prop :=
  vinogradovWeylLow r ≤ j.val + 1 ∧ j.val + 1 ≤ vinogradovWeylHigh r

instance (r : ℕ) : DecidablePred (vinogradovWeylUseful r) := fun j => by
  unfold vinogradovWeylUseful; infer_instance

/-- The size threshold `P₀ = max(2⁴⁸, (384 b² k)²)`. -/
def vinogradovWeylThreshold (r : ℕ) : ℕ :=
  max (2 ^ 48) ((384 * vinogradovWeylMoment r ^ 2 * vinogradovWeylDegree r) ^ 2)

/-- The constant `M_r = (C_{k,b}² (24b²)^k)^{1/(4b²)}`. -/
def vinogradovWeylConstant (r : ℕ) : ℝ :=
  (vinogradovExplicitConstant (vinogradovWeylDegree r) (vinogradovWeylMoment r) ^ 2 *
    (24 * (vinogradovWeylMoment r : ℝ) ^ 2) ^ vinogradovWeylDegree r) ^
      ((((4 * vinogradovWeylMoment r ^ 2 : ℕ) : ℝ))⁻¹)

/-- The number of useful coordinates. -/
def vinogradovWeylCount (r : ℕ) : ℕ := vinogradovWeylHigh r + 1 - vinogradovWeylLow r

/-- The saving exponent `δ_r = (n_r ⌊r/4⌋ - 2)/(4b²)`. -/
def vinogradovWeylSaving (r : ℕ) : ℝ :=
  ((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) - 2 : ℝ) /
    (4 * (vinogradovWeylMoment r : ℝ) ^ 2)

theorem three_le_vinogradovWeylDegree {r : ℕ} (hr : 1 ≤ r) : 3 ≤ vinogradovWeylDegree r := by
  unfold vinogradovWeylDegree; omega

theorem one_le_vinogradovWeylMoment (r : ℕ) : 1 ≤ vinogradovWeylMoment r := by
  unfold vinogradovWeylMoment vinogradovWeylDegree
  have : 1 ≤ (2 * r + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have : 1 ≤ Nat.log 2 ((2 * r + 2) * (2 * r + 2 + 1) / 2) + 1 := Nat.le_add_left 1 _
  nlinarith

/-- The mean value defect is below one. -/
theorem vinogradovWeyl_defect_lt_one {r : ℕ} (hr : 1 ≤ r) :
    (vinogradovWeylDegree r * (vinogradovWeylDegree r + 1) / 2 : ℝ) *
        (1 - 1 / (vinogradovWeylDegree r : ℝ)) ^
          ((vinogradovWeylMoment r : ℝ) / vinogradovWeylDegree r) < 1 := by
  set k := vinogradovWeylDegree r with hk
  set m := Nat.log 2 (vinogradovWeylK r) + 1 with hm
  have hk3 : 3 ≤ k := three_le_vinogradovWeylDegree hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hexp := rpow_one_sub_inv_le_exp (k := k) (by omega) (vinogradovWeylMoment r)
  have hbk : ((vinogradovWeylMoment r : ℕ) : ℝ) / (k : ℝ) ^ 2 = m := by
    rw [vinogradovWeylMoment, ← hk, ← hm]
    push_cast
    field_simp
  rw [hbk] at hexp
  have hKcast : (k * (k + 1) / 2 : ℝ) = (vinogradovWeylK r : ℝ) := by
    rw [vinogradovWeylK, ← hk, Nat.cast_div (Nat.even_mul_succ_self k).two_dvd (by norm_num)]
    push_cast; ring
  have hlt : vinogradovWeylK r < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) _
  have hltR : (vinogradovWeylK r : ℝ) < 2 ^ m := by exact_mod_cast hlt
  have h2e : (2 : ℝ) ^ m ≤ Real.exp m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
    have := Real.log_two_lt_d9
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hK0 : (0 : ℝ) ≤ vinogradovWeylK r := Nat.cast_nonneg _
  have hexpneg : Real.exp (-(m : ℝ)) = (Real.exp m)⁻¹ := Real.exp_neg _
  rw [hKcast]
  calc (vinogradovWeylK r : ℝ) * (1 - 1 / (k : ℝ)) ^ ((vinogradovWeylMoment r : ℝ) / k)
      ≤ (vinogradovWeylK r : ℝ) * Real.exp (-(m : ℝ)) := mul_le_mul_of_nonneg_left hexp hK0
    _ = (vinogradovWeylK r : ℝ) / Real.exp m := by rw [hexpneg]; ring
    _ < 1 := by
        rw [div_lt_one (Real.exp_pos _)]
        linarith

/-- `2πd·162^d ≤ 2^{12d}`. -/
theorem two_pi_mul_mul_pow_le {d : ℕ} (hd : 1 ≤ d) :
    2 * Real.pi * d * (162 : ℝ) ^ d ≤ (2 : ℝ) ^ (12 * d) := by
  have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_d2]
  have hd2 : (d : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h162 : (162 : ℝ) ^ d ≤ (2 : ℝ) ^ (8 * d) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (3 * d) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc 2 * Real.pi * d * (162 : ℝ) ^ d ≤ 8 * (2 : ℝ) ^ d * (2 : ℝ) ^ (8 * d) := by gcongr
    _ ≤ (2 : ℝ) ^ (3 * d) * (2 : ℝ) ^ d * (2 : ℝ) ^ (8 * d) := by gcongr
    _ = (2 : ℝ) ^ (12 * d) := by rw [← pow_add, ← pow_add]; ring_nf

/-- Upper window: `α (P^{2e} + 1) ≤ 1`. -/
theorem logTaylorMagnitude_mul_le_one {t x P : ℝ} {k e r : ℕ} (hP : 1 ≤ P)
    (ht2 : t ≤ P ^ (4 * r + 4)) (hx : 4 * P ^ 4 ≤ x) (j : Fin k)
    (hwin : 4 * r + 4 + 2 * e ≤ 4 * (j.val + 1)) :
    logTaylorMagnitude t x j * (P ^ (2 * e) + 1) ≤ 1 := by
  set d := j.val + 1 with hd
  have hP0 : 0 < P := by linarith
  have h4P : 0 < 4 * P ^ 4 := by positivity
  have hx0 : 0 < x := by linarith
  have hxd : (4 * P ^ 4) ^ d ≤ x ^ d := pow_le_pow_left₀ (by positivity) hx d
  have h4d : (4 : ℝ) ≤ 4 ^ d := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith [Real.pi_gt_three]
  have hdR : ((j.val : ℝ) + 1) = (d : ℝ) := by rw [hd]; push_cast; ring
  unfold logTaylorMagnitude
  rw [← hd, hdR]
  have hden : 4 * P ^ (4 * d) ≤ 2 * Real.pi * d * x ^ d := by
    calc 4 * P ^ (4 * d) ≤ 4 ^ d * (P ^ 4) ^ d := by
          rw [← pow_mul]; exact mul_le_mul_of_nonneg_right h4d (by positivity)
      _ = (4 * P ^ 4) ^ d := (mul_pow _ _ _).symm
      _ ≤ x ^ d := hxd
      _ ≤ 2 * Real.pi * d * x ^ d := le_mul_of_one_le_left (by positivity) hpi
  have hpow : P ^ (4 * r + 4) * P ^ (2 * e) ≤ P ^ (4 * d) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP hwin
  have h2e : P ^ (2 * e) + 1 ≤ 2 * P ^ (2 * e) := by
    have : (1 : ℝ) ≤ P ^ (2 * e) := one_le_pow₀ hP
    linarith
  rw [div_mul_eq_mul_div, div_le_one (by positivity)]
  calc t * (P ^ (2 * e) + 1) ≤ P ^ (4 * r + 4) * (2 * P ^ (2 * e)) :=
        mul_le_mul ht2 h2e (by positivity) (by positivity)
    _ = 2 * (P ^ (4 * r + 4) * P ^ (2 * e)) := by ring
    _ ≤ 2 * P ^ (4 * d) := by linarith
    _ ≤ 4 * P ^ (4 * d) := by linarith [pow_nonneg hP0.le (4 * d)]
    _ ≤ 2 * Real.pi * d * x ^ d := hden

/-- Lower window: `P^{2e} ≤ α P^{2(j+1)}`. -/
theorem le_logTaylorMagnitude_mul {t x P : ℝ} {k e r : ℕ} (hP : (2 : ℝ) ^ 48 ≤ P)
    (ht1 : P ^ (4 * r) ≤ t) (hx0 : 0 < x) (hx : x ≤ 162 * P ^ 4) (j : Fin k)
    (hwin : 9 * (j.val + 1) + 8 * e ≤ 16 * r) :
    P ^ (2 * e) ≤ logTaylorMagnitude t x j * P ^ (2 * (j.val + 1)) := by
  set d := j.val + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hP1 : (1 : ℝ) ≤ P := le_trans (one_le_pow₀ (by norm_num)) hP
  have hP0 : 0 < P := by linarith
  have hconst := two_pi_mul_mul_pow_le hd1
  -- `(2^{12d})^4 ≤ P^d`
  have hc4 : ((2 : ℝ) ^ (12 * d)) ^ 4 ≤ P ^ d := by
    rw [← pow_mul, show 12 * d * 4 = 48 * d by ring, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hP d
  have hxd : x ^ d ≤ (162 * P ^ 4) ^ d := pow_le_pow_left₀ hx0.le hx d
  -- it suffices: `2πd 162^d P^{2d+2e} ≤ P^{4r}`
  have hkey : 2 * Real.pi * d * (162 : ℝ) ^ d * P ^ (2 * d + 2 * e) ≤ P ^ (4 * r) := by
    have h4 : (2 * Real.pi * d * (162 : ℝ) ^ d * P ^ (2 * d + 2 * e)) ^ 4 ≤ (P ^ (4 * r)) ^ 4 := by
      have hA0 : 0 ≤ 2 * Real.pi * d * (162 : ℝ) ^ d := by positivity
      calc (2 * Real.pi * d * (162 : ℝ) ^ d * P ^ (2 * d + 2 * e)) ^ 4
          = (2 * Real.pi * d * (162 : ℝ) ^ d) ^ 4 * P ^ (8 * d + 8 * e) := by
            rw [mul_pow, ← pow_mul]; ring_nf
        _ ≤ ((2 : ℝ) ^ (12 * d)) ^ 4 * P ^ (8 * d + 8 * e) := by
            gcongr
        _ ≤ P ^ d * P ^ (8 * d + 8 * e) := by gcongr
        _ = P ^ (9 * d + 8 * e) := by rw [← pow_add]; ring_nf
        _ ≤ P ^ (16 * r) := pow_le_pow_right₀ hP1 hwin
        _ = (P ^ (4 * r)) ^ 4 := by rw [← pow_mul]; ring_nf
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4
  have hdR : ((j.val : ℝ) + 1) = (d : ℝ) := by rw [hd]; push_cast; ring
  unfold logTaylorMagnitude
  rw [← hd, hdR, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc P ^ (2 * e) * (2 * Real.pi * d * x ^ d)
      ≤ P ^ (2 * e) * (2 * Real.pi * d * (162 * P ^ 4) ^ d) := by gcongr
    _ = 2 * Real.pi * d * (162 : ℝ) ^ d * P ^ (2 * d + 2 * e) * P ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]; ring_nf
    _ ≤ P ^ (4 * r) * P ^ (2 * d) := by gcongr
    _ ≤ t * P ^ (2 * d) := by gcongr

/-- Absorption: `32b²(1 + log(2/α)) ≤ P^e`. -/
theorem absorb_le_pow {t x P : ℝ} {k e r b : ℕ} (hP : (2 : ℝ) ^ 48 ≤ P)
    (hPb : ((384 * b ^ 2 * k) ^ 2 : ℕ) ≤ P) (he : 1 ≤ e) (ht1 : P ^ (4 * r) ≤ t)
    (hx0 : 0 < x) (hx : x ≤ 162 * P ^ 4) (j : Fin k) :
    32 * (b : ℝ) ^ 2 * (1 + Real.log (2 / logTaylorMagnitude t x j)) ≤ P ^ e := by
  set d := j.val + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hdk : d ≤ k := j.isLt
  have hP1 : (1 : ℝ) ≤ P := le_trans (one_le_pow₀ (by norm_num)) hP
  have hP0 : 0 < P := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hα0 := logTaylorMagnitude_pos (k := k) ht0 hx0 j
  -- `2/α ≤ 2^{13d} P^{4d}`
  have hinv : 2 / logTaylorMagnitude t x j ≤ (2 : ℝ) ^ (13 * d) * P ^ (4 * d) := by
    have hdR : ((j.val : ℝ) + 1) = (d : ℝ) := by rw [hd]; push_cast; ring
    unfold logTaylorMagnitude
    rw [← hd, hdR]
    have hconst := two_pi_mul_mul_pow_le hd1
    have ht1' : (1 : ℝ) ≤ t := le_trans (one_le_pow₀ hP1) ht1
    rw [div_div_eq_mul_div, div_le_iff₀ ht0]
    have hxd : x ^ d ≤ (162 * P ^ 4) ^ d := pow_le_pow_left₀ hx0.le hx d
    calc 2 * (2 * Real.pi * d * x ^ d) ≤ 2 * (2 * Real.pi * d * (162 * P ^ 4) ^ d) := by gcongr
      _ = 2 * (2 * Real.pi * d * (162 : ℝ) ^ d) * P ^ (4 * d) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ 2 * (2 : ℝ) ^ (12 * d) * P ^ (4 * d) := by gcongr
      _ ≤ (2 : ℝ) ^ (13 * d) * P ^ (4 * d) := by
          gcongr
          calc 2 * (2 : ℝ) ^ (12 * d) = 2 ^ (12 * d + 1) := by ring
            _ ≤ 2 ^ (13 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (2 : ℝ) ^ (13 * d) * P ^ (4 * d) * t := le_mul_of_one_le_right (by positivity) ht1'
  have hlogP : (1 : ℝ) ≤ Real.log P := by
    rw [Real.le_log_iff_exp_le hP0]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (3 : ℝ) ≤ 2 ^ 48 := by norm_num
    linarith
  have h2P : (2 : ℝ) ^ 13 ≤ P := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hP
  have hlog : Real.log (2 / logTaylorMagnitude t x j) ≤ 5 * d * Real.log P := by
    have hpos : 0 < 2 / logTaylorMagnitude t x j := by positivity
    calc Real.log (2 / logTaylorMagnitude t x j) ≤ Real.log ((2 : ℝ) ^ (13 * d) * P ^ (4 * d)) :=
          Real.log_le_log hpos hinv
      _ = 13 * d * Real.log 2 + 4 * d * Real.log P := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
      _ ≤ d * Real.log P + 4 * d * Real.log P := by
          have : 13 * Real.log 2 ≤ Real.log P := by
            rw [← Real.log_rpow (by norm_num)]
            exact Real.log_le_log (by positivity) (by exact_mod_cast h2P)
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
          nlinarith
      _ = 5 * d * Real.log P := by ring
  -- `log P ≤ 2√P`, and `√P ≥ 384 b² k`
  have hsqrt : Real.log P ≤ 2 * Real.sqrt P := by
    have h := Real.log_le_rpow_div (x := P) (ε := 1 / 2) hP0.le (by norm_num)
    rw [Real.sqrt_eq_rpow]
    linarith
  have hsq : (384 * (b : ℝ) ^ 2 * k) ≤ Real.sqrt P := by
    apply Real.le_sqrt_of_sq_le
    have : (((384 * b ^ 2 * k) ^ 2 : ℕ) : ℝ) ≤ P := hPb
    push_cast at this
    linarith
  have hsqP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
  have hPe : P ≤ P ^ e := by
    calc P = P ^ 1 := (pow_one _).symm
      _ ≤ P ^ e := pow_le_pow_right₀ hP1 he
  have hdR : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hb0 : (0 : ℝ) ≤ (b : ℝ) ^ 2 := by positivity
  calc 32 * (b : ℝ) ^ 2 * (1 + Real.log (2 / logTaylorMagnitude t x j))
      ≤ 32 * (b : ℝ) ^ 2 * (6 * d * Real.log P) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = 192 * (b : ℝ) ^ 2 * d * Real.log P := by ring
    _ ≤ 192 * (b : ℝ) ^ 2 * k * (2 * Real.sqrt P) := by
        gcongr
    _ = (384 * (b : ℝ) ^ 2 * k) * Real.sqrt P := by ring
    _ ≤ Real.sqrt P * Real.sqrt P := by gcongr
    _ = P := hsqP
    _ ≤ P ^ e := hPe


/-- The useful coordinates number at least `n_r`. -/
theorem le_card_vinogradovWeylUseful {r : ℕ} (hr : 4 ≤ r) :
    vinogradovWeylCount r ≤
      ((Finset.univ : Finset (Fin (vinogradovWeylDegree r))).filter
        (vinogradovWeylUseful r)).card := by
  classical
  have hlow1 : 1 ≤ vinogradovWeylLow r := by unfold vinogradovWeylLow; omega
  have hhighk : vinogradovWeylHigh r ≤ vinogradovWeylDegree r := by
    unfold vinogradovWeylHigh vinogradovWeylDegree; omega
  let f : Fin (vinogradovWeylCount r) → Fin (vinogradovWeylDegree r) := fun n =>
    ⟨vinogradovWeylLow r - 1 + n.val, by
      have := n.isLt
      unfold vinogradovWeylCount at this
      omega⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [f] at this
    omega
  have himg : (Finset.univ.image f) ⊆
      (Finset.univ : Finset (Fin (vinogradovWeylDegree r))).filter (vinogradovWeylUseful r) := by
    intro j hj
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [f]; omega
    · have := n.isLt
      unfold vinogradovWeylCount at this
      simp only [f]
      omega
  calc vinogradovWeylCount r = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card himg

/-- **Vinogradov's estimate for `Σ n^{it}`.** -/
theorem norm_sum_logPhase_le_vinogradov {r Q A L : ℕ} {t : ℝ} (hr : 4 ≤ r)
    (hP : vinogradovWeylThreshold r ≤ 2 * Q)
    (ht1 : ((2 * Q : ℕ) : ℝ) ^ (4 * r) ≤ t) (ht2 : t ≤ ((2 * Q : ℕ) : ℝ) ^ (4 * r + 4))
    (hA : 4 * (2 * Q) ^ 4 ≤ A) (hAL : A + L ≤ 162 * (2 * Q) ^ 4) :
    ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖ ≤
      4 * vinogradovWeylConstant r * L * ((2 * Q : ℕ) : ℝ) ^ (-vinogradovWeylSaving r) +
        400 * ((2 * Q : ℕ) : ℝ) ^ 2 := by
  classical
  set k := vinogradovWeylDegree r with hk
  set b := vinogradovWeylMoment r with hb
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hPdef
  have hk3 : 3 ≤ k := three_le_vinogradovWeylDegree (by omega)
  have hb1 : 1 ≤ b := one_le_vinogradovWeylMoment r
  have hP48 : (2 : ℝ) ^ 48 ≤ P := by
    rw [hPdef]
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    exact_mod_cast this
  have hPb : ((384 * b ^ 2 * k) ^ 2 : ℕ) ≤ P := by
    rw [hPdef]
    have : (384 * b ^ 2 * k) ^ 2 ≤ 2 * Q := le_trans (le_max_right _ _) hP
    exact_mod_cast this
  have hP1 : (1 : ℝ) ≤ P := le_trans (one_le_pow₀ (by norm_num)) hP48
  have hP0 : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := by
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    have h1 : 1 ≤ 2 ^ 48 := Nat.one_le_two_pow
    omega
  have hQP : (Q : ℝ) = P / 2 := by rw [hPdef]; push_cast; ring
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set U := vinogradovWeylUseful r with hU
  set e : Fin k → ℕ := fun _ => vinogradovWeylSave r with he
  have hsave1 : 1 ≤ vinogradovWeylSave r := by unfold vinogradovWeylSave; omega
  -- the bound at each point
  set Mfull : ℝ := vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k with hMfull
  set D : ℝ := (k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k) with hD
  have hD1 : D < 1 := vinogradovWeyl_defect_lt_one (by omega)
  have hD0 : 0 ≤ D := by
    have := Real.rpow_nonneg (rpow_one_sub_inv_pos (k := k) (by omega)).le ((b : ℝ) / k)
    rw [hD]; positivity
  set SU : ℕ := ∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j with hSU
  have hSU : vinogradovWeylCount r * vinogradovWeylSave r ≤ SU := by
    rw [hSU, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (le_card_vinogradovWeylUseful hr)
  have hMfull0 : 0 ≤ Mfull := by
    have := (vinogradovExplicitConstant_pos k b).le
    rw [hMfull]; positivity
  set bb : ℝ := (((4 * b ^ 2 : ℕ) : ℝ))⁻¹ with hbb
  have hbb0 : 0 < bb := by rw [hbb]; positivity
  have hpoint : ∀ x ∈ Finset.Ioc A (A + L),
      ‖routeTLogRatioBilinearSum t (x : ℝ) Q‖ ≤
        vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) + 1 / 2 := by
    intro x hx
    have hxI := Finset.mem_Ioc.mp hx
    have hxlow : 4 * P ^ 4 ≤ (x : ℝ) := by
      have : 4 * (2 * Q) ^ 4 ≤ x := by omega
      rw [hPdef]; exact_mod_cast this
    have hxup : (x : ℝ) ≤ 162 * P ^ 4 := by
      have : x ≤ 162 * (2 * Q) ^ 4 := by omega
      rw [hPdef]; exact_mod_cast this
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hxlow
    have hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) := by
      rw [← hPdef]
      have : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
      linarith
    have hW4 := norm_routeTLogRatioBilinearSum_le_explicit (b := b) ht0 hx0 hk3 hb1 hQ1 hscale
      U e
      (fun j hj => by
        have := hj.1
        simp only [he, vinogradovWeylSave]
        unfold vinogradovWeylLow at this
        omega)
      (fun j hj => le_logTaylorMagnitude_mul hP48 ht1 hx0 hxup j (by
        have := hj.2
        simp only [he, vinogradovWeylSave]
        unfold vinogradovWeylHigh at this
        omega))
      (fun j hj => logTaylorMagnitude_mul_le_one hP1 ht2 hxlow j (by
        have := hj.1
        simp only [he, vinogradovWeylSave]
        unfold vinogradovWeylLow at this
        omega))
      (fun j _ => absorb_le_pow hP48 hPb hsave1 ht1 hx0 hxup j)
    -- first term
    have hfirst : (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb ≤
        vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) := by
      have hsplit : (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb =
          Mfull ^ bb * P ^ ((8 * (b : ℝ) ^ 2 + 2 * D - SU) * bb) := by
        have hPSU : (P ^ SU)⁻¹ = P ^ (-(SU : ℝ)) := by
          rw [Real.rpow_neg hP0.le, Real.rpow_natCast]
        rw [hPSU, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow hMfull0 (by positivity), ← Real.rpow_mul hP0.le,
          ← Real.rpow_mul hP0.le, mul_assoc, ← Real.rpow_add hP0]
        congr 2
        ring
      have hMconst : Mfull ^ bb = vinogradovWeylConstant r := by
        rw [hMfull, hbb, vinogradovWeylConstant]
      rw [hsplit, hMconst]
      apply mul_le_mul_of_nonneg_left _ (by
        rw [← hMconst]; exact Real.rpow_nonneg hMfull0 _)
      apply Real.rpow_le_rpow_of_exponent_le hP1
      have hb2 : (0 : ℝ) < 4 * (b : ℝ) ^ 2 := by positivity
      have hbbv : bb = 1 / (4 * (b : ℝ) ^ 2) := by rw [hbb]; push_cast; ring
      have hSUR : ((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) : ℝ) ≤ (SU : ℝ) := by
        exact_mod_cast hSU
      rw [hbbv, vinogradovWeylSaving]
      rw [show 2 - (((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) : ℝ) - 2) /
          (4 * (b : ℝ) ^ 2) = (8 * (b : ℝ) ^ 2 + 2 - ((vinogradovWeylCount r *
            vinogradovWeylSave r : ℕ) : ℝ)) * (1 / (4 * (b : ℝ) ^ 2)) by field_simp; ring]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    -- second term
    have hsecond : 2 * Real.pi * (t / Real.pi * (P ^ 2 / x) ^ (k + 1)) *
        (Q : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [hQP]
      have hratio : P ^ 2 / (x : ℝ) ≤ 1 / (4 * P ^ 2) := by
        rw [div_le_div_iff₀ hx0 (by positivity)]
        have e : P ^ 2 * (4 * P ^ 2) = 4 * P ^ 4 := by ring
        linarith
      have hr0 : 0 ≤ P ^ 2 / (x : ℝ) := by positivity
      have hpow : (P ^ 2 / (x : ℝ)) ^ (k + 1) ≤ (1 / (4 * P ^ 2)) ^ (k + 1) :=
        pow_le_pow_left₀ hr0 hratio _
      have hk1 : k + 1 = 2 * r + 3 := by rw [hk]; unfold vinogradovWeylDegree; ring
      have h4 : (1 / (4 * P ^ 2)) ^ (k + 1) ≤ 1 / (4 * P ^ (4 * r + 6)) := by
        rw [hk1, div_pow, one_pow, mul_pow, ← pow_mul]
        apply one_div_le_one_div_of_le (by positivity)
        have : (4 : ℝ) ≤ 4 ^ (2 * r + 3) := by
          calc (4 : ℝ) = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ (2 * r + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [show 2 * (2 * r + 3) = 4 * r + 6 by ring]
        exact mul_le_mul_of_nonneg_right this (by positivity)
      have hpi : 0 < Real.pi := Real.pi_pos
      calc 2 * Real.pi * (t / Real.pi * (P ^ 2 / (x : ℝ)) ^ (k + 1)) * (P / 2) ^ 2
          = 2 * t * (P ^ 2 / (x : ℝ)) ^ (k + 1) * (P / 2) ^ 2 := by field_simp
        _ ≤ 2 * P ^ (4 * r + 4) * (1 / (4 * P ^ (4 * r + 6))) * (P / 2) ^ 2 := by
            gcongr
            exact hpow.trans h4
        _ = 1 / 8 := by
            field_simp
            ring
        _ ≤ 1 / 2 := by norm_num
    calc ‖routeTLogRatioBilinearSum t (x : ℝ) Q‖
        ≤ (Mfull * P ^ (8 * (b : ℝ) ^ 2 + 2 * D) * (P ^ SU)⁻¹) ^ bb +
            2 * Real.pi * (t / Real.pi * (P ^ 2 / x) ^ (k + 1)) *
              (Q : ℝ) ^ 2 := hW4
      _ ≤ _ := add_le_add hfirst hsecond
  -- assemble
  have hshift := sq_mul_norm_sum_logPhase_le (t := t) (A := A) (L := L) (Q := Q) (by
    have : 4 * Q ^ 2 ≤ 4 * (2 * Q) ^ 4 := by
      have : Q ^ 2 ≤ (2 * Q) ^ 4 := by
        calc Q ^ 2 ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ ≤ (2 * Q) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    omega)
  have hsum : ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t (x : ℝ) Q‖ ≤
      L * (vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) + 1 / 2) := by
    calc _ ≤ ∑ _x ∈ Finset.Ioc A (A + L),
          (vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) + 1 / 2) :=
          Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; congr 2; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hLP : (L : ℝ) ≤ 162 * P ^ 4 := by
    have : L ≤ 162 * (2 * Q) ^ 4 := by omega
    rw [hPdef]; exact_mod_cast this
  have hM0 : 0 ≤ vinogradovWeylConstant r := Real.rpow_nonneg (by
    have := (vinogradovExplicitConstant_pos k b).le
    positivity) _
  have hpowsplit : P ^ (2 - vinogradovWeylSaving r) = P ^ 2 * P ^ (-vinogradovWeylSaving r) := by
    rw [sub_eq_add_neg, Real.rpow_add hP0, Real.rpow_two]
  set S := ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖
  have hmain : (Q : ℝ) ^ 2 * S ≤
      L * (vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) + 1 / 2) +
        8 * (Q : ℝ) ^ 4 := by
    have h := add_le_add hsum (le_refl (8 * (Q : ℝ) ^ 4))
    exact hshift.trans h
  rw [hQP] at hmain
  have hP2 : 0 < (P / 2) ^ 2 := by positivity
  have hS : S ≤ (L * (vinogradovWeylConstant r * P ^ (2 - vinogradovWeylSaving r) + 1 / 2) +
      8 * (P / 2) ^ 4) / (P / 2) ^ 2 := by
    rw [le_div_iff₀ hP2]; linarith
  refine hS.trans ?_
  rw [div_le_iff₀ hP2, hpowsplit]
  set M := vinogradovWeylConstant r
  set w := P ^ (-vinogradovWeylSaving r)
  have e1 : (4 * M * L * w + 400 * P ^ 2) * (P / 2) ^ 2 = M * L * (P ^ 2 * w) + 100 * P ^ 4 := by
    ring
  have e2 : (L : ℝ) * (M * (P ^ 2 * w) + 1 / 2) + 8 * (P / 2) ^ 4 =
      M * L * (P ^ 2 * w) + L / 2 + P ^ 4 / 2 := by ring
  rw [e1, e2]
  linarith [pow_nonneg hP0.le 4]

end

end RHTower.Sieve
