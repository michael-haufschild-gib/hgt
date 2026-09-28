import GaloisForLFunctions.RHTower.Sieve.ShiuAdaptiveCut

/-!
# Shiu's bound for `t^{ω(n)}` in short intervals

For `0 ≤ t ≤ 1` and every `y ≥ √A`,

`∑_{A < n ≤ A+y} t^{ω(n)} ≤ C · y · (log A)^{t-1}`

with an absolute `C` (`shiu_omegaTilt_short_interval`).

The proof is Shiu's.  Each `n > z` is cut as `n = b·a` at the least smoothness bound `q` at which the
`q`-smooth part of `n` exceeds `z` (`shiuLevel`): `b ≤ z` collects the prime powers below `q`, `a`
those from `q` on, and `q ∣ a`.  With `w = ⌊√z⌋`, either `q > w` (then `a` is `w`-rough and the
Selberg sieve counts it with density `2/log w`), or `q ≤ w` and `b ≤ w` (then `n` has a prime-power
divisor `q^e > w` with `q ≤ w`, a sparse event), or `q ≤ w < b` (then `a` has no prime factor up to
`P⁺(b)` and Rankin's trick at the exponent `1/log P⁺(b)` pays for the size of `b`).  Rankin's bound
for tilted smooth sums, `∑_{b W-smooth} t^{ω(b)} b^{σ-1} ≤ exp(t(log log W + C))` at `σ = 1/log W`,
supplies the Euler products.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-! ## The explicit bound -/

/-- **Case II, summed.** -/
theorem shiu_caseII_sum_le {w : ℕ} (hw : 1 ≤ w) (y : ℕ) :
    ∑ q ∈ Nat.primesLE w, ((y : ℝ) / ((q ^ shiuPowExp w q : ℕ) : ℝ) + 1)
      ≤ (y : ℝ) / Real.sqrt w * mertensS w + w := by
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hsw : 0 < Real.sqrt (w : ℝ) := Real.sqrt_pos.2 (by linarith)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine add_le_add ?_ ?_
  · rw [mertensS, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hqp := Nat.prime_of_mem_primesLE hq
    have hqw : q ≤ w := (Nat.mem_primesLE.1 hq).1
    have hq2 := hqp.two_le
    set e := shiuPowExp w q with he
    have hlt : w < q ^ e := lt_pow_shiuPowExp hq2
    have he2 : 2 ≤ e := by
      by_contra hcon
      push Not at hcon
      interval_cases e
      · simp at hlt; omega
      · simp at hlt; omega
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
    have hpowR : (q : ℝ) ^ (2 : ℕ) ≤ ((q ^ e : ℕ) : ℝ) := by
      push_cast; exact pow_le_pow_right₀ (by exact_mod_cast hqp.one_lt.le) he2
    have hwpow : (w : ℝ) < ((q ^ e : ℕ) : ℝ) := by exact_mod_cast hlt
    have hkey : (q : ℝ) * Real.sqrt w ≤ ((q ^ e : ℕ) : ℝ) := by
      have h0 : 0 ≤ (q : ℝ) * Real.sqrt w := by positivity
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      have hQ0 : (0 : ℝ) ≤ ((q ^ e : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hpowR, hwpow, sq_nonneg (q : ℝ)]
    rw [show (y : ℝ) / Real.sqrt w * (1 / (q : ℝ)) = (y : ℝ) / ((q : ℝ) * Real.sqrt w) by
      field_simp]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hkey
  · have := Finset.card_le_card (show Nat.primesLE w ⊆ Finset.Icc 1 w by
      intro q hq
      exact Finset.mem_Icc.2 ⟨(Nat.prime_of_mem_primesLE hq).one_lt.le,
        (Nat.mem_primesLE.1 hq).1⟩)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this

/-- The fibre length. -/
theorem div_sub_div_le {A y b : ℕ} (hb : 0 < b) :
    (((A + y) / b : ℕ) : ℝ) - ((A / b : ℕ) : ℝ) ≤ (y : ℝ) / b + 1 := by
  obtain ⟨h1, -⟩ := cast_div_bounds (d := b) (n := A + y) hb
  obtain ⟨-, h2⟩ := cast_div_bounds (d := b) (n := A) hb
  have e : ((A + y : ℕ) : ℝ) / b = (A : ℝ) / b + (y : ℝ) / b := by push_cast; ring
  linarith

/-- **Shiu's bound for `t^{ω(n)}`, explicit form.** -/
theorem shiu_omegaTilt_explicit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y z w : ℕ}
    (hz1 : 1 ≤ z) (hzA : z ≤ A) (hwz : w * w ≤ z) (hw2 : 2 ≤ w) (hz4 : 4 ≤ Real.log z)
    (hwlog : Real.log z - 1 ≤ 2 * Real.log w) :
    ∑ n ∈ Finset.Ioc A (A + y), omegaTilt t n
      ≤ 2 * (y : ℝ) / Real.log w * Real.exp (t * (logLog z + rankinTiltConst))
        + (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
        + ((y : ℝ) / Real.sqrt w * mertensS w + w)
        + (2 * (y : ℝ) * (20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
              / Real.log z
            + (1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
              * Real.exp (1 * (logLog 55 + rankinTiltConst))))
          + (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hz2 : 2 ≤ z := le_trans (by nlinarith) hwz
  rw [sum_omegaTilt_Ioc_eq_cases t A y z w]
  refine add_le_add (add_le_add ?_ ((shiu_caseII_le ht0 ht1 hz1 hzA hwz).trans
    (shiu_caseII_sum_le (by omega) y))) ?_
  · -- case I
    refine (shiu_caseI_le ht0 ht1 hz1 hzA).trans ?_
    have hterm : ∀ b ∈ Finset.Icc 1 z, omegaTilt t b
        * (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE w, ¬ p ∣ m)).card : ℝ)
        ≤ 2 * (y : ℝ) / Real.log w * (omegaTilt t b / (b : ℝ))
          + (2 / Real.log w + selbergFibreError w w) := by
      intro b hb
      have hb0 : 0 < b := (Finset.mem_Icc.1 hb).1
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
      have hsieve := card_rough_Ioc_le_selberg (A / b) ((A + y) / b) w w
        (Nat.div_le_div_right (by omega)) (by omega) le_rfl hw2 hlogw
      have hlen := div_sub_div_le (A := A) (y := y) hb0
      have hE := selbergFibreError_nonneg hw2 w
      have hω0 := omegaTilt_nonneg ht0 b
      have hω1 := omegaTilt_le_one ht0 ht1 b
      have hcount : (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE w, ¬ p ∣ m)).card : ℝ)
          ≤ ((y : ℝ) / b + 1) * (2 / Real.log w) + selbergFibreError w w :=
        hsieve.trans (add_le_add (mul_le_mul_of_nonneg_right hlen (by positivity)) le_rfl)
      calc omegaTilt t b * (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE w, ¬ p ∣ m)).card : ℝ)
          ≤ omegaTilt t b * (((y : ℝ) / b + 1) * (2 / Real.log w) + selbergFibreError w w) :=
            mul_le_mul_of_nonneg_left hcount hω0
        _ = 2 * (y : ℝ) / Real.log w * (omegaTilt t b / (b : ℝ))
            + omegaTilt t b * (2 / Real.log w + selbergFibreError w w) := by
            field_simp
            ring
        _ ≤ 2 * (y : ℝ) / Real.log w * (omegaTilt t b / (b : ℝ))
            + (2 / Real.log w + selbergFibreError w w) := by
            have : 0 ≤ 2 / Real.log w + selbergFibreError w w := by positivity
            nlinarith [hω1, this]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    refine add_le_add (mul_le_mul_of_nonneg_left (sum_Icc_omegaTilt_div_le ht0 hz4)
      (by positivity)) le_rfl
  · -- case III
    refine (shiu_caseIII_le ht0 ht1 hz1 hzA).trans ?_
    have hterm : ∀ b ∈ Finset.Ioc w z, omegaTilt t b
        * (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE (largestPrime b), ¬ p ∣ m)).card : ℝ)
        ≤ 2 * (y : ℝ) * (omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b)))
          + (2 / Real.log 2 + selbergFibreError z z) := by
      intro b hb
      obtain ⟨hwb, hbz⟩ := Finset.mem_Ioc.1 hb
      have hb0 : 0 < b := by omega
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
      have hP2 : 2 ≤ largestPrime b := two_le_largestPrime (by omega)
      have hPz : largestPrime b ≤ z := le_trans (largestPrime_le b) hbz
      have hlogP : Real.log 2 ≤ Real.log (largestPrime b) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hP2)
      have hlogP0 : 0 < Real.log (largestPrime b) := by linarith
      have hsieve := card_rough_Ioc_le_selberg (A / b) ((A + y) / b) (largestPrime b)
        (largestPrime b) (Nat.div_le_div_right (by omega)) (by omega) le_rfl hP2 hlogP0
      have hlen := div_sub_div_le (A := A) (y := y) hb0
      have hEmono : selbergFibreError (largestPrime b) (largestPrime b) ≤ selbergFibreError z z := by
        rw [selbergFibreError, selbergFibreError]
        have hPR : (2 : ℝ) ≤ (largestPrime b : ℝ) := by exact_mod_cast hP2
        have hPzR : (largestPrime b : ℝ) ≤ (z : ℝ) := by exact_mod_cast hPz
        have h1 : ((largestPrime b * largestPrime b : ℕ) : ℝ) ≤ ((z * z : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul hPz hPz
        have h2 : (Real.log (largestPrime b)) ^ (4 : ℝ) ≤ (Real.log z) ^ (4 : ℝ) :=
          Real.rpow_le_rpow hlogP0.le (Real.log_le_log (by linarith) hPzR) (by norm_num)
        have hE : 0 < Real.exp (4 * mertensSecondUpperConst) := Real.exp_pos _
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hE.le) (by positivity) (by positivity)
      have hω0 := omegaTilt_nonneg ht0 b
      have hω1 := omegaTilt_le_one ht0 ht1 b
      have hcount : (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE (largestPrime b), ¬ p ∣ m)).card : ℝ)
          ≤ ((y : ℝ) / b + 1) * (2 / Real.log (largestPrime b)) + selbergFibreError z z :=
        hsieve.trans (add_le_add (mul_le_mul_of_nonneg_right hlen (by positivity)) hEmono)
      have hinv : 2 / Real.log (largestPrime b) ≤ 2 / Real.log 2 :=
        div_le_div_of_nonneg_left (by norm_num) hlog2 hlogP
      calc omegaTilt t b * (((Finset.Ioc (A / b) ((A + y) / b)).filter
            (fun m => ∀ p ∈ Nat.primesLE (largestPrime b), ¬ p ∣ m)).card : ℝ)
          ≤ omegaTilt t b * (((y : ℝ) / b + 1) * (2 / Real.log (largestPrime b))
              + selbergFibreError z z) := mul_le_mul_of_nonneg_left hcount hω0
        _ = 2 * (y : ℝ) * (omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b)))
            + omegaTilt t b * (2 / Real.log (largestPrime b) + selbergFibreError z z) := by
            field_simp
            ring
        _ ≤ 2 * (y : ℝ) * (omegaTilt t b / ((b : ℝ) * Real.log (largestPrime b)))
            + (2 / Real.log 2 + selbergFibreError z z) := by
            have hE0 := selbergFibreError_nonneg hz2 z
            have h1 : omegaTilt t b * (2 / Real.log (largestPrime b) + selbergFibreError z z)
                ≤ 1 * (2 / Real.log (largestPrime b) + selbergFibreError z z) :=
              mul_le_mul_of_nonneg_right hω1 (by positivity)
            linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    refine add_le_add (mul_le_mul_of_nonneg_left
      (sum_omegaTilt_div_log_largestPrime_le ht0 ht1 hw2 hz4 hwlog) (by positivity)) ?_
    refine mul_le_mul_of_nonneg_right ?_ (by
      have := selbergFibreError_nonneg hz2 z
      positivity)
    have : z - w ≤ z := Nat.sub_le z w
    exact_mod_cast this

/-- The main-term constant of Shiu's bound. -/
def shiuMainConst : ℝ := (128 + 640 * Real.exp (1 / 8)) * Real.exp |rankinTiltConst|

/-- **Shiu's bound from explicit conditions on the scale.**  With `L = log A`, `log z ≥ L/16`,
`log w ≥ (log z − 1)/2`, and all secondary terms below `√A/L`, every interval `(A, A+y]` with
`√A ≤ y ≤ A` has `∑ t^{ω(n)} ≤ (shiuMainConst + 5)·y·L^{t−1}`. -/
theorem shiu_omegaTilt_of_conditions {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y z w : ℕ}
    (hz1 : 1 ≤ z) (hzA : z ≤ A) (hwz : w * w ≤ z) (hw2 : 2 ≤ w) (hz4 : 4 ≤ Real.log z)
    (hwlog : Real.log z - 1 ≤ 2 * Real.log w)
    (hL1 : 1 ≤ Real.log A) (hzL : Real.log A / 16 ≤ Real.log z)
    (hsec1 : (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
        + (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z) + w
      ≤ Real.sqrt A / Real.log A)
    (hsec2 : mertensS w / Real.sqrt w ≤ 1 / Real.log A)
    (hsec3 : 2 * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
        * Real.exp (1 * (logLog 55 + rankinTiltConst)))) ≤ 1 / Real.log A)
    (hyA : A ≤ y * y) :
    ∑ n ∈ Finset.Ioc A (A + y), omegaTilt t n
      ≤ (shiuMainConst + 3) * (y : ℝ) * (Real.log A) ^ (t - 1) := by
  have hexpl := shiu_omegaTilt_explicit (A := A) (y := y) ht0 ht1 hz1 hzA hwz hw2 hz4 hwlog
  refine hexpl.trans ?_
  set L : ℝ := Real.log A with hLdef
  have hL0 : 0 < L := by linarith
  have hlogz0 : 0 < Real.log (z : ℝ) := by linarith
  have hlogw : Real.log z / 4 ≤ Real.log w := by linarith
  have hlogw0 : 0 < Real.log (w : ℝ) := by linarith
  have hyR : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
  -- `(log z)^{t-1} ≤ 16 L^{t-1}`
  have hpow : (Real.log z) ^ (t - 1) ≤ 16 * L ^ (t - 1) := by
    have h1 : (Real.log z) ^ (t - 1) ≤ (L / 16) ^ (t - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hzL (by linarith)
    have h2 : (L / 16) ^ (t - 1) = (16 : ℝ) ^ (1 - t) * L ^ (t - 1) := by
      rw [Real.div_rpow hL0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_sub, mul_comm]
    have h3 : (16 : ℝ) ^ (1 - t) ≤ 16 := by
      calc (16 : ℝ) ^ (1 - t) ≤ (16 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 16 := Real.rpow_one 16
    rw [h2] at h1
    have hLp : 0 ≤ L ^ (t - 1) := Real.rpow_nonneg hL0.le _
    nlinarith [h1, h3, hLp]
  have hLpow_pos : 0 < L ^ (t - 1) := Real.rpow_pos_of_pos hL0 _
  -- `exp(t(log log z + C)) ≤ exp|C| · (log z)^t`
  have hexpC : Real.exp (t * (logLog z + rankinTiltConst))
      ≤ Real.exp |rankinTiltConst| * (Real.log z) ^ t := by
    rw [mul_add, Real.exp_add, logLog, mul_comm t (Real.log (Real.log z)),
      ← Real.rpow_def_of_pos hlogz0, mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hlogz0.le _)
    calc t * rankinTiltConst ≤ |t * rankinTiltConst| := le_abs_self _
      _ = t * |rankinTiltConst| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ 1 * |rankinTiltConst| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |rankinTiltConst| := one_mul _
  have hzt : (Real.log z) ^ t / Real.log z = (Real.log z) ^ (t - 1) := by
    rw [Real.rpow_sub hlogz0, Real.rpow_one]
  -- the two main terms
  have hmain1 : 2 * (y : ℝ) / Real.log w * Real.exp (t * (logLog z + rankinTiltConst))
      ≤ 128 * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1) := by
    have h1 : 2 * (y : ℝ) / Real.log w ≤ 8 * (y : ℝ) / Real.log z := by
      rw [div_le_div_iff₀ hlogw0 hlogz0]; nlinarith [hlogw, hyR]
    calc 2 * (y : ℝ) / Real.log w * Real.exp (t * (logLog z + rankinTiltConst))
        ≤ 8 * (y : ℝ) / Real.log z * (Real.exp |rankinTiltConst| * (Real.log z) ^ t) :=
          mul_le_mul h1 hexpC (Real.exp_pos _).le (by positivity)
      _ = 8 * Real.exp |rankinTiltConst| * (y : ℝ) * ((Real.log z) ^ t / Real.log z) := by ring
      _ ≤ 8 * Real.exp |rankinTiltConst| * (y : ℝ) * (16 * L ^ (t - 1)) := by
          rw [hzt]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 128 * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1) := by ring
  have hmain2 : 2 * (y : ℝ) * (20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
        / Real.log z)
      ≤ 640 * Real.exp (1 / 8) * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1) := by
    calc 2 * (y : ℝ) * (20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
          / Real.log z)
        ≤ 2 * (y : ℝ) * (20 * Real.exp (1 / 8)
            * (Real.exp |rankinTiltConst| * (Real.log z) ^ t) / Real.log z) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexpC (by positivity)) hlogz0.le) (by positivity)
      _ = 40 * Real.exp (1 / 8) * Real.exp |rankinTiltConst| * (y : ℝ)
            * ((Real.log z) ^ t / Real.log z) := by ring
      _ ≤ 40 * Real.exp (1 / 8) * Real.exp |rankinTiltConst| * (y : ℝ) * (16 * L ^ (t - 1)) := by
          rw [hzt]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 640 * Real.exp (1 / 8) * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1) := by ring
  -- the secondary terms against `y L^{t-1}`
  have hsqrt : Real.sqrt (A : ℝ) ≤ (y : ℝ) := by
    rw [show (y : ℝ) = Real.sqrt ((y : ℝ) * (y : ℝ)) by rw [Real.sqrt_mul_self hyR]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hyA)
  have hinvL : 1 / L ≤ L ^ (t - 1) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsec1' : (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
        + (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z) + w
      ≤ (y : ℝ) * L ^ (t - 1) := by
    refine hsec1.trans ?_
    calc Real.sqrt A / L = Real.sqrt A * (1 / L) := by ring
      _ ≤ (y : ℝ) * L ^ (t - 1) :=
          mul_le_mul hsqrt hinvL (by positivity) hyR
  have hsec2' : (y : ℝ) / Real.sqrt w * mertensS w ≤ (y : ℝ) * L ^ (t - 1) := by
    calc (y : ℝ) / Real.sqrt w * mertensS w = (y : ℝ) * (mertensS w / Real.sqrt w) := by ring
      _ ≤ (y : ℝ) * (1 / L) := mul_le_mul_of_nonneg_left hsec2 hyR
      _ ≤ (y : ℝ) * L ^ (t - 1) := mul_le_mul_of_nonneg_left hinvL hyR
  have hsec3' : 2 * (y : ℝ) * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
        * Real.exp (1 * (logLog 55 + rankinTiltConst)))) ≤ (y : ℝ) * L ^ (t - 1) := by
    calc 2 * (y : ℝ) * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
          * Real.exp (1 * (logLog 55 + rankinTiltConst))))
        = (y : ℝ) * (2 * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
          * Real.exp (1 * (logLog 55 + rankinTiltConst))))) := by ring
      _ ≤ (y : ℝ) * (1 / L) := mul_le_mul_of_nonneg_left hsec3 hyR
      _ ≤ (y : ℝ) * L ^ (t - 1) := mul_le_mul_of_nonneg_left hinvL hyR
  rw [shiuMainConst]
  have e : ((128 + 640 * Real.exp (1 / 8)) * Real.exp |rankinTiltConst| + 3) * (y : ℝ)
        * L ^ (t - 1)
      = 128 * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1)
        + 640 * Real.exp (1 / 8) * Real.exp |rankinTiltConst| * (y : ℝ) * L ^ (t - 1)
        + 3 * ((y : ℝ) * L ^ (t - 1)) := by ring
  rw [e]
  have hsplit : 2 * (y : ℝ) * (20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
          / Real.log z
        + (1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
          * Real.exp (1 * (logLog 55 + rankinTiltConst))))
      = 2 * (y : ℝ) * (20 * Real.exp (1 / 8) * Real.exp (t * (logLog z + rankinTiltConst))
          / Real.log z)
        + 2 * (y : ℝ) * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55))
          * Real.exp (1 * (logLog 55 + rankinTiltConst)))) := by ring
  rw [hsplit]
  linarith [hmain1, hmain2, hsec1', hsec2', hsec3']

/-! ## The asymptotic bound -/

/-- The cut scale `z ≈ A^{1/8}`. -/
def shiuCut (A : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt A))

theorem shiuCut_pow_le (A : ℕ) : shiuCut A ^ 8 ≤ A := by
  have h1 := Nat.sqrt_le' A
  have h2 := Nat.sqrt_le' (Nat.sqrt A)
  have h3 := Nat.sqrt_le' (Nat.sqrt (Nat.sqrt A))
  rw [shiuCut]
  set a := Nat.sqrt A
  set b := Nat.sqrt a
  set c := Nat.sqrt b
  calc c ^ 8 = ((c ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ (b ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) 2
    _ ≤ a ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ A := h1

theorem lt_succ_shiuCut_pow (A : ℕ) : A < (shiuCut A + 1) ^ 8 := by
  have h1 := Nat.lt_succ_sqrt' A
  have h2 := Nat.lt_succ_sqrt' (Nat.sqrt A)
  have h3 := Nat.lt_succ_sqrt' (Nat.sqrt (Nat.sqrt A))
  rw [shiuCut]
  set a := Nat.sqrt A
  set b := Nat.sqrt a
  set c := Nat.sqrt b
  have ha : a + 1 ≤ (b + 1) ^ 2 := h2
  have hb : b + 1 ≤ (c + 1) ^ 2 := h3
  calc A < (a + 1) ^ 2 := h1
    _ ≤ ((b + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left ha 2
    _ ≤ (((c + 1) ^ 2) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hb 2) 2
    _ = (c + 1) ^ 8 := by ring

/-- `log (n+1) ≤ log n + 1/n`. -/
theorem log_succ_le_log_add_inv {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ Real.log n + 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have e : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
  rw [e, Real.log_mul hnR.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
  linarith

theorem eventually_shiu_scale_one {E : ℝ} (hE : 0 < E) :
    ∀ᶠ s : ℝ in atTop, (7 + 2 * E * s ^ (4 : ℕ)) * s ≤ Real.exp (s / 8) := by
  have hlo := isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 8 by norm_num)
  filter_upwards [hlo.bound (show (0 : ℝ) < 1 / (7 + 2 * E) by positivity),
    eventually_ge_atTop (1 : ℝ)] with s hs hs1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  have h4 : (1 : ℝ) ≤ s ^ (4 : ℕ) := one_le_pow₀ hs1
  have hsmul : (7 + 2 * E * s ^ (4 : ℕ)) * s ≤ (7 + 2 * E) * s ^ (5 : ℕ) := by
    have e : (7 + 2 * E) * s ^ (5 : ℕ) = 7 * s ^ (4 : ℕ) * s + 2 * E * s ^ (4 : ℕ) * s := by ring
    rw [e]
    have : 7 * s ≤ 7 * s ^ (4 : ℕ) * s := by nlinarith only [h4, hs1]
    nlinarith only [this]
  have e : Real.exp (1 / 8 * s) = Real.exp (s / 8) := by ring_nf
  rw [e] at hs
  calc (7 + 2 * E * s ^ (4 : ℕ)) * s ≤ (7 + 2 * E) * s ^ (5 : ℕ) := hsmul
    _ ≤ (7 + 2 * E) * (1 / (7 + 2 * E) * Real.exp (s / 8)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Real.exp (s / 8) := by field_simp

theorem eventually_shiu_scale_two (c : ℝ) :
    ∀ᶠ s : ℝ in atTop, (s + c) * s * Real.exp (1 / 2) ≤ Real.exp (s / 32) := by
  have hlo := isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 / 32 by norm_num)
  set k : ℝ := (1 + |c|) * Real.exp (1 / 2) with hk
  have hk0 : 0 < k := by rw [hk]; positivity
  filter_upwards [hlo.bound (show (0 : ℝ) < 1 / k by positivity),
    eventually_ge_atTop (1 : ℝ)] with s hs hs1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  have e : Real.exp (1 / 32 * s) = Real.exp (s / 32) := by ring_nf
  rw [e] at hs
  have hc : s + c ≤ (1 + |c|) * s := by
    have h1 := le_abs_self c
    have h2 : |c| ≤ |c| * s := le_mul_of_one_le_right (abs_nonneg c) hs1
    nlinarith only [h1, h2]
  have he : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have h1 : (s + c) * s * Real.exp (1 / 2) ≤ k * s ^ (2 : ℕ) := by
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg (by linarith : (0 : ℝ) ≤ s) he.le)
    rw [hk]
    nlinarith only [this]
  calc (s + c) * s * Real.exp (1 / 2) ≤ k * s ^ (2 : ℕ) := h1
    _ ≤ k * (1 / k * Real.exp (s / 32)) := mul_le_mul_of_nonneg_left hs hk0.le
    _ = Real.exp (s / 32) := by field_simp

theorem eventually_shiu_scale_three {K : ℝ} (hK : 0 < K) :
    ∀ᶠ s : ℝ in atTop, 2 * (1 / Real.log 2) * K * s
      ≤ Real.exp ((s / 16 - 2 * Real.log 2) / Real.log 55) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl55 : 0 < Real.log 55 := by have := four_le_log_55; linarith
  have hlo := isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 / (16 * Real.log 55) by
    positivity)
  set k : ℝ := 2 * (1 / Real.log 2) * K * Real.exp (2 * Real.log 2 / Real.log 55) with hk
  have hk0 : 0 < k := by rw [hk]; positivity
  filter_upwards [hlo.bound (show (0 : ℝ) < 1 / k by positivity),
    eventually_ge_atTop (0 : ℝ)] with s hs hs0
  rw [pow_one, Real.norm_of_nonneg hs0, Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  have e : Real.exp ((s / 16 - 2 * Real.log 2) / Real.log 55)
      = Real.exp (1 / (16 * Real.log 55) * s) / Real.exp (2 * Real.log 2 / Real.log 55) := by
    rw [← Real.exp_sub]; congr 1; field_simp
  rw [e, le_div_iff₀ (Real.exp_pos _)]
  have : k * s ≤ Real.exp (1 / (16 * Real.log 55) * s) := by
    calc k * s ≤ k * (1 / k * Real.exp (1 / (16 * Real.log 55) * s)) :=
          mul_le_mul_of_nonneg_left hs hk0.le
      _ = Real.exp (1 / (16 * Real.log 55) * s) := by field_simp
  have e2 : 2 * (1 / Real.log 2) * K * s * Real.exp (2 * Real.log 2 / Real.log 55) = k * s := by
    rw [hk]; ring
  rw [e2]; exact this

/-- **Shiu's bound at one scale**, from the three largeness conditions on `log A`. -/
theorem shiu_omegaTilt_at_scale {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A y : ℕ}
    (hA1 : (7 + 2 * Real.exp (4 * mertensSecondUpperConst) * (Real.log A) ^ (4 : ℕ))
        * Real.log A ≤ Real.exp (Real.log A / 8))
    (hA2 : (Real.log A + mertensSecondUpperConst) * Real.log A * Real.exp (1 / 2)
        ≤ Real.exp (Real.log A / 32))
    (hA3 : 2 * (1 / Real.log 2) * Real.exp (1 * (logLog 55 + rankinTiltConst)) * Real.log A
        ≤ Real.exp ((Real.log A / 16 - 2 * Real.log 2) / Real.log 55))
    (hA200 : 200 ≤ Real.log A) (hyA : A ≤ y * y) :
    ∑ n ∈ Finset.Ioc A (A + y), omegaTilt t n
      ≤ (shiuMainConst + 3) * (y : ℝ) * (Real.log A) ^ (t - 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2half : 1 / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h55 := four_le_log_55
  obtain ⟨E4, hE4⟩ : ∃ E, Real.exp (4 * mertensSecondUpperConst) = E := ⟨_, rfl⟩
  obtain ⟨K55, hK55⟩ : ∃ K, Real.exp (1 * (logLog 55 + rankinTiltConst)) = K := ⟨_, rfl⟩
  have hE40 : 0 < E4 := hE4 ▸ Real.exp_pos _
  have hK0 : 0 < K55 := hK55 ▸ Real.exp_pos _
  rw [hE4] at hA1
  rw [hK55] at hA3
  obtain ⟨sA, hsA⟩ : ∃ s, Real.log (A : ℝ) = s := ⟨_, rfl⟩
  rw [hsA] at hA1 hA2 hA3 hA200 ⊢
  have hA0 : 0 < A := by
    by_contra h
    have : A = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hsA
    linarith
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA0
  obtain ⟨z, hz⟩ : ∃ z, shiuCut A = z := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, Nat.sqrt z = w := ⟨_, rfl⟩
  have hz8 : z ^ 8 ≤ A := hz ▸ shiuCut_pow_le A
  have hzlt : A < (z + 1) ^ 8 := hz ▸ lt_succ_shiuCut_pow A
  have hz1 : 1 ≤ z := by
    by_contra hcon
    have : z = 0 := by omega
    rw [this] at hzlt
    norm_num at hzlt
    omega
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hlogz_up : 8 * Real.log z ≤ sA := by
    have := Real.log_le_log (by positivity)
      (show ((z ^ 8 : ℕ) : ℝ) ≤ (A : ℝ) by exact_mod_cast hz8)
    push_cast at this; rw [Real.log_pow, hsA] at this; push_cast at this; linarith only [this]
  have hlogz_low : sA ≤ 8 * (Real.log z + 1) := by
    have h1 := Real.log_le_log hAR (show (A : ℝ) ≤ (((z + 1) ^ 8 : ℕ) : ℝ) by
      exact_mod_cast hzlt.le)
    push_cast at h1; rw [Real.log_pow, hsA] at h1; push_cast at h1
    have h2 := log_succ_le_log_add_inv hz1
    have h3 : 1 / (z : ℝ) ≤ 1 := by rw [div_le_one (by linarith only [hzR])]; exact hzR
    linarith only [h1, h2, h3]
  have hwz : w * w ≤ z := hw ▸ Nat.sqrt_le z
  have hwlt : z < (w + 1) * (w + 1) := hw ▸ Nat.lt_succ_sqrt z
  have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg hzR
  have hlogzbig : 24 ≤ Real.log (z : ℝ) := by linarith only [hlogz_low, hA200]
  have hw1 : 1 ≤ w := by
    by_contra hcon
    have : w = 0 := by omega
    rw [this] at hwlt
    have : z = 0 := by omega
    omega
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
  have hlogw_up : 2 * Real.log w ≤ Real.log z := by
    have := Real.log_le_log (by positivity)
      (show ((w * w : ℕ) : ℝ) ≤ (z : ℝ) by exact_mod_cast hwz)
    push_cast at this; rw [Real.log_mul (by positivity) (by positivity)] at this
    linarith only [this]
  have hlogw_low : Real.log z ≤ 2 * (Real.log w + 1 / (w : ℝ)) := by
    have h1 := Real.log_le_log (by positivity) (show (z : ℝ) ≤ (((w + 1) * (w + 1) : ℕ) : ℝ) by
      exact_mod_cast hwlt.le)
    push_cast at h1; rw [Real.log_mul (by positivity) (by positivity)] at h1
    have h2 := log_succ_le_log_add_inv hw1
    linarith only [h1, h2]
  have hinvw1 : 1 / (w : ℝ) ≤ 1 := by rw [div_le_one (by linarith only [hwR])]; exact hwR
  have hw2 : 2 ≤ w := by
    by_contra hcon
    have : w = 1 := by omega
    rw [this] at hlogw_low
    simp only [Nat.cast_one, Real.log_one, zero_add, div_one] at hlogw_low
    linarith only [hlogw_low, hlogzbig]
  have hwR2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw2
  have hinvw : 1 / (w : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith only [hwR2]) (by norm_num)]; linarith only [hwR2]
  have hwlog : Real.log z - 1 ≤ 2 * Real.log w := by linarith only [hlogw_low, hinvw]
  have hlogw_low1 : sA / 16 - 1 ≤ Real.log w := by
    linarith only [hlogw_low, hinvw, hlogz_low]
  have hlogw_lowA : sA / 16 - 2 * Real.log 2 ≤ Real.log w := by
    linarith only [hlogw_low1, hlog2half]
  have hlogw0 : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith only [hwR2])
  have hzexp : (z : ℝ) ≤ Real.exp (sA / 8) := by
    rw [← Real.exp_log (show (0 : ℝ) < (z : ℝ) by linarith only [hzR])]
    exact Real.exp_le_exp.2 (by linarith only [hlogz_up])
  have hwz' : (w : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans (hw ▸ Nat.sqrt_le_self z) le_rfl
  -- the secondary terms
  have hEw : selbergFibreError w w ≤ E4 * (z : ℝ) * sA ^ (4 : ℕ) := by
    rw [selbergFibreError, hE4]
    have h1 : ((w * w : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hwz
    have h2 : Real.log (w : ℝ) ^ (4 : ℝ) ≤ sA ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ hlogw0.le (by linarith only [hlogw_up, hlogz_up, hlogw0]) 4
    have := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hE40.le) (by positivity) (by positivity)
    linarith only [this]
  have hEz : selbergFibreError z z ≤ E4 * ((z : ℝ) * (z : ℝ)) * sA ^ (4 : ℕ) := by
    rw [selbergFibreError, hE4]
    have h2 : Real.log (z : ℝ) ^ (4 : ℝ) ≤ sA ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ hlogz0 (by linarith only [hlogz_up, hlogz0]) 4
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hE40.le)
      (show (0 : ℝ) ≤ ((z * z : ℕ) : ℝ) by positivity)
    push_cast at this ⊢
    linarith only [this]
  have hsec1 : (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
        + (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z) + w
      ≤ Real.sqrt A / sA := by
    have hsqrtA : Real.exp (sA / 2) = Real.sqrt A := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hAR, hsA]; ring_nf
    have hz3 : (z : ℝ) ^ (3 : ℕ) ≤ Real.exp (3 * (sA / 8)) := by
      rw [show 3 * (sA / 8) = (3 : ℕ) * (sA / 8) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith only [hzR]) hzexp 3
    have hlog2inv : 2 / Real.log 2 ≤ 3 := by
      rw [div_le_iff₀ hlog2]; have := Real.log_two_gt_d9; linarith only [this]
    have hlog2w : 2 / Real.log w ≤ 3 :=
      (div_le_div_of_nonneg_left (by norm_num) hlog2
        (Real.log_le_log (by norm_num) hwR2)).trans hlog2inv
    have hsA4 : 0 ≤ sA ^ (4 : ℕ) := by positivity
    have hzz : (z : ℝ) * (z : ℝ) ≤ (z : ℝ) ^ (3 : ℕ) := by nlinarith only [hzR]
    have hz1' : (z : ℝ) ≤ (z : ℝ) ^ (3 : ℕ) := by nlinarith only [hzR, hzz]
    have t1 : (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
        ≤ 3 * (z : ℝ) + E4 * ((z : ℝ) * (z : ℝ)) * sA ^ (4 : ℕ) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hlog2w hEw) (by linarith only [hzR] :
        (0 : ℝ) ≤ (z : ℝ))
      linarith only [this]
    have t2 : (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z)
        ≤ 3 * (z : ℝ) + E4 * (z : ℝ) ^ (3 : ℕ) * sA ^ (4 : ℕ) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hlog2inv hEz) (by linarith only [hzR] :
        (0 : ℝ) ≤ (z : ℝ))
      have e : (z : ℝ) * (3 + E4 * ((z : ℝ) * (z : ℝ)) * sA ^ (4 : ℕ))
          = 3 * (z : ℝ) + E4 * (z : ℝ) ^ (3 : ℕ) * sA ^ (4 : ℕ) := by ring
      linarith only [this, e]
    have hbound : (z : ℝ) * (2 / Real.log w + selbergFibreError w w)
          + (z : ℝ) * (2 / Real.log 2 + selbergFibreError z z) + w
        ≤ (7 + 2 * E4 * sA ^ (4 : ℕ)) * (z : ℝ) ^ (3 : ℕ) := by
      have h1 : E4 * ((z : ℝ) * (z : ℝ)) * sA ^ (4 : ℕ) ≤ E4 * (z : ℝ) ^ (3 : ℕ) * sA ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzz hE40.le) hsA4
      linarith only [t1, t2, h1, hz1', hwz']
    refine hbound.trans ?_
    rw [le_div_iff₀ (by linarith only [hA200]), ← hsqrtA]
    have h3 := mul_le_mul_of_nonneg_left hz3
      (show (0 : ℝ) ≤ 7 + 2 * E4 * sA ^ (4 : ℕ) by positivity)
    have e : Real.exp (sA / 2) = Real.exp (3 * (sA / 8)) * Real.exp (sA / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    calc (7 + 2 * E4 * sA ^ (4 : ℕ)) * (z : ℝ) ^ (3 : ℕ) * sA
        ≤ (7 + 2 * E4 * sA ^ (4 : ℕ)) * Real.exp (3 * (sA / 8)) * sA :=
          mul_le_mul_of_nonneg_right h3 (by linarith only [hA200])
      _ = Real.exp (3 * (sA / 8)) * ((7 + 2 * E4 * sA ^ (4 : ℕ)) * sA) := by ring
      _ ≤ Real.exp (3 * (sA / 8)) * Real.exp (sA / 8) :=
          mul_le_mul_of_nonneg_left hA1 (Real.exp_pos _).le
  have hsec2 : mertensS w / Real.sqrt w ≤ 1 / sA := by
    have hM := mertensS_le hw2
    have hll : logLog w ≤ sA := by
      rw [logLog]
      have h1 : Real.log (Real.log w) ≤ Real.log w - 1 := Real.log_le_sub_one_of_pos hlogw0
      linarith only [h1, hlogw_up, hlogz_up, hA200, hlogw0]
    have hsw : Real.exp (sA / 32 - 1 / 2) ≤ Real.sqrt w := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith only [hwR])]
      exact Real.exp_le_exp.2 (by linarith only [hlogw_low1])
    have hsw0 : 0 < Real.sqrt (w : ℝ) := Real.sqrt_pos.2 (by linarith only [hwR])
    rw [div_le_div_iff₀ hsw0 (by linarith only [hA200]), one_mul]
    have e : Real.exp (sA / 32 - 1 / 2) * Real.exp (1 / 2) = Real.exp (sA / 32) := by
      rw [← Real.exp_add]; ring_nf
    have hkey : (sA + mertensSecondUpperConst) * sA ≤ Real.exp (sA / 32 - 1 / 2) := by
      rw [← mul_le_mul_iff_left₀ (Real.exp_pos (1 / 2)), e]; exact hA2
    calc mertensS w * sA ≤ (sA + mertensSecondUpperConst) * sA :=
          mul_le_mul_of_nonneg_right (by linarith only [hM, hll]) (by linarith only [hA200])
      _ ≤ Real.exp (sA / 32 - 1 / 2) := hkey
      _ ≤ Real.sqrt w := hsw
  have hsec3 : 2 * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55)) * K55)) ≤ 1 / sA := by
    have hl55 : 0 < Real.log 55 := by linarith only [h55]
    have hwpow : (w : ℝ) ^ (-(1 / Real.log 55))
        ≤ Real.exp (-((sA / 16 - 2 * Real.log 2) / Real.log 55)) := by
      rw [Real.rpow_def_of_pos (by linarith only [hwR])]
      refine Real.exp_le_exp.2 ?_
      rw [mul_neg, neg_le_neg_iff, mul_one_div]
      exact div_le_div_of_nonneg_right hlogw_lowA hl55.le
    rw [le_div_iff₀ (by linarith only [hA200])]
    have h1 := mul_le_mul_of_nonneg_left hwpow
      (show (0 : ℝ) ≤ 2 * (1 / Real.log 2) * K55 * sA by
        have : (0 : ℝ) ≤ sA := by linarith only [hA200]
        positivity)
    have e : 2 * (1 / Real.log 2) * K55 * sA
          * Real.exp (-((sA / 16 - 2 * Real.log 2) / Real.log 55))
        = 2 * (1 / Real.log 2) * K55 * sA
          / Real.exp ((sA / 16 - 2 * Real.log 2) / Real.log 55) := by
      rw [Real.exp_neg]; ring
    have h2 : 2 * (1 / Real.log 2) * K55 * sA
        / Real.exp ((sA / 16 - 2 * Real.log 2) / Real.log 55) ≤ 1 := by
      rw [div_le_one (Real.exp_pos _)]; exact hA3
    have e2 : 2 * ((1 / Real.log 2) * ((w : ℝ) ^ (-(1 / Real.log 55)) * K55)) * sA
        = 2 * (1 / Real.log 2) * K55 * sA * (w : ℝ) ^ (-(1 / Real.log 55)) := by ring
    rw [e2]
    linarith only [h1, e, h2]
  have hzA : z ≤ A := le_trans (Nat.le_self_pow (by norm_num) z) hz8
  have hz4 : 4 ≤ Real.log (z : ℝ) := by linarith only [hlogzbig]
  have hzL : sA / 16 ≤ Real.log z := by linarith only [hlogz_low, hA200]
  have key := shiu_omegaTilt_of_conditions (A := A) (y := y) ht0 ht1 hz1 hzA hwz hw2 hz4 hwlog
    (by rw [hsA]; linarith only [hA200]) (by rw [hsA]; exact hzL) (by rw [hsA]; exact hsec1)
    (by rw [hsA]; exact hsec2) (by rw [hsA, hK55]; exact hsec3) hyA
  rw [hsA] at key
  exact key

/-- **Shiu's bound for `t^{ω(n)}` on short intervals.**  For `0 ≤ t ≤ 1`, uniformly in
`y ≥ √A`, `∑_{A < n ≤ A+y} t^{ω(n)} ≤ C y (log A)^{t-1}` with an absolute `C`. -/
theorem shiu_omegaTilt_short_interval {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᶠ A : ℕ in atTop, ∀ y : ℕ, A ≤ y * y →
      ∑ n ∈ Finset.Ioc A (A + y), omegaTilt t n
        ≤ (shiuMainConst + 3) * (y : ℝ) * (Real.log A) ^ (t - 1) := by
  have hlogA : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogA.eventually (eventually_shiu_scale_one
      (Real.exp_pos (4 * mertensSecondUpperConst))),
    hlogA.eventually (eventually_shiu_scale_two mertensSecondUpperConst),
    hlogA.eventually (eventually_shiu_scale_three
      (Real.exp_pos (1 * (logLog 55 + rankinTiltConst)))),
    hlogA.eventually_ge_atTop (200 : ℝ)] with A hA1 hA2 hA3 hA200
  intro y hyA
  exact shiu_omegaTilt_at_scale ht0 ht1 hA1 hA2 hA3 hA200 hyA

end

end RHTower.Sieve
