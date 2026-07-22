/-
# Depth-one rigidity of functional-equation × integrality × multiplicativity

A single integral Dirichlet factor `1 − a·b^{−s}` carries its zeros on one vertical line: from
`a·b^{−s} = 1` taking norms gives `‖a‖·b^{−Re s} = 1`, so `Re s = log‖a‖ / log b`.  The functional
equation reflects the line `σ` to `1 − σ`; realizing the reflected line by *integral* data at the
same base `b` demands a factorization `a·a′ = b`, since two lines `log a/log b` and `log a′/log b`
sum to `1` exactly when `log a + log a′ = log b`, i.e. `a·a′ = b`.

The three hypotheses interact as follows.

* **Prime frequency `b = p`.**  The only factorizations `a·a′ = p` are the walls `a = 1` or `a′ = 1`:
  no off-line integral mirror pair exists.
* **Composite non-prime-power frequency `b = 6`.**  Off-line pairs do exist — `log 2/log 6 + log 3/log 6 = 1`
  with `log 2/log 6 ≠ 1/2` — but a stream supported off the primes at frequency `6` is *not*
  multiplicative: multiplicativity would force the coefficient at `6 = 2·3` to be the product of the
  (zero) coefficients at the coprime `2` and `3`.
* **Multiplicative column `b = p^k`.**  Unique factorization forces every integral divisor of `p^k`
  to be a prime power `p^i`, so every admissible zero-line is quantized to `log(p^i)/log(p^k) = i/k`,
  and `σ = 1/2` is the unique self-dual quantized line (`i/k = 1 − i/k ↔ 2i = k`).

Each single hypothesis dropped has a witness; only the conjunction rigidifies.  The naive
infinite-depth limit of the quantization `{i/k}` is dense in `(0,1)`, so the depth-one mechanism
merely exhibits the interaction; the surviving content at full depth is the coherence across columns.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs

noncomputable section

namespace RHTower

open Complex

/-! ### §1 A single integral factor lives on one vertical line -/

/-- **The zero-line of a single factor.**  If `1 − A·b^{−s} = 0` with `A ≠ 0` and `b ≥ 2`, then
`Re s = log‖A‖ / log b`: from `A·b^{−s} = 1` take norms, `‖A‖·b^{−Re s} = 1`, and apply `log`. -/
theorem factor_zero_line {A : ℂ} (hA : A ≠ 0) {b : ℕ} (hb : 2 ≤ b) {s : ℂ}
    (h : 1 - A * (b : ℂ) ^ (-s) = 0) : s.re = Real.log ‖A‖ / Real.log b := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le one_lt_two hb
  have hbpos : (0 : ℝ) < b := lt_trans one_pos hb1
  have hLne : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb1)
  have hAne : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  have heq : A * (b : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖A‖ * ‖(b : ℂ) ^ (-s)‖ = 1 := by rw [← norm_mul, heq, norm_one]
  have hcp : ‖(b : ℂ) ^ (-s)‖ = (b : ℝ) ^ (-s.re) := by
    rw [← Complex.ofReal_natCast b, Complex.norm_cpow_eq_rpow_re_of_pos hbpos, Complex.neg_re]
  rw [hcp] at hnorm
  have hlog : Real.log ‖A‖ + (-s.re) * Real.log b = 0 := by
    have hc := congrArg Real.log hnorm
    rwa [Real.log_mul hAne (by positivity), Real.log_rpow hbpos, Real.log_one] at hc
  rw [eq_div_iff hLne]; linarith

/-- **Converse existence.**  For integers `a > 1` and `b ≥ 2` there is a zero of `1 − a·b^{−s}` on the
line `Re s = log a / log b`, realized by the real point `s₀ = log a / log b` where `b^{−s₀} = 1/a`. -/
theorem exists_zero_on_line {a : ℕ} (ha : 1 < a) {b : ℕ} (hb : 2 ≤ b) :
    ∃ s : ℂ, 1 - (a : ℂ) * (b : ℂ) ^ (-s) = 0 ∧ s.re = Real.log a / Real.log b := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le one_lt_two hb
  have hbpos : (0 : ℝ) < b := lt_trans one_pos hb1
  have haR : (0 : ℝ) < a := by exact_mod_cast lt_trans one_pos ha
  have haCne : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one ha))
  have hlogbne : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb1)
  refine ⟨((Real.log a / Real.log b : ℝ) : ℂ), ?_, Complex.ofReal_re _⟩
  have hreal : (b : ℝ) ^ (-(Real.log a / Real.log b)) = 1 / a := by
    rw [Real.rpow_def_of_pos hbpos,
      show Real.log b * (-(Real.log a / Real.log b)) = -Real.log a by field_simp,
      Real.exp_neg, Real.exp_log haR]; ring
  have hcexp : (b : ℂ) ^ (-((Real.log a / Real.log b : ℝ) : ℂ)) = ((1 / a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast b, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (le_of_lt hbpos), hreal]
  rw [hcexp]; push_cast; rw [mul_one_div, div_self haCne]; ring

/-! ### §2 Prime frequency admits only the wall pairs -/

/-- **Prime frequency is wall-rigid.**  A factorization `a·a′ = p` of a prime forces `a = 1` or
`a′ = 1`: `a ∣ p` gives `a = 1 ∨ a = p`, and `a = p` cancels to `a′ = 1`. -/
theorem prime_frequency_wall_rigidity {p : ℕ} (hp : p.Prime) {a a' : ℕ}
    (ha : a * a' = p) : a = 1 ∨ a' = 1 := by
  rcases hp.eq_one_or_self_of_dvd a ⟨a', ha.symm⟩ with h1 | hp'
  · exact Or.inl h1
  · right
    have hapos : 0 < a := by rw [hp']; exact hp.pos
    have heq : a * a' = a * 1 := by rw [mul_one]; exact ha.trans hp'.symm
    exact Nat.eq_of_mul_eq_mul_left hapos heq

/-- **No off-line integral mirror pair at a prime.**  Two nontrivial factors `1 < a`, `1 < a′` never
multiply to a prime `p`. -/
theorem prime_frequency_no_offline_pair {p : ℕ} (hp : p.Prime) {a a' : ℕ}
    (ha1 : 1 < a) (ha'1 : 1 < a') : a * a' ≠ p := by
  intro h
  rcases prime_frequency_wall_rigidity hp h with h1 | h1 <;> omega

/-! ### §3 The functional-equation pairing is a factorization -/

/-- **Mirror integrality is factorization.**  Two integral zero-lines at the same base sum to `1`
exactly when their frequencies multiply to the base: `log a/log b + log a′/log b = 1 ↔ a·a′ = b`, by
log-additivity and injectivity of `log` on the positives. -/
theorem mirror_line_integral_iff {a a' b : ℕ} (ha : 1 ≤ a) (ha' : 1 ≤ a') (hb : 2 ≤ b) :
    Real.log a / Real.log b + Real.log a' / Real.log b = 1 ↔ a * a' = b := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le one_lt_two hb
  have hlogbne : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb1)
  have haRne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  have ha'Rne : (a' : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha')
  have hbRpos : (0 : ℝ) < b := lt_trans one_pos hb1
  have hlogmul : Real.log a + Real.log a' = Real.log ((a * a' : ℕ)) := by
    push_cast; rw [Real.log_mul haRne ha'Rne]
  constructor
  · intro h
    rw [← add_div, div_eq_one_iff_eq hlogbne, hlogmul] at h
    have hpos : (0 : ℝ) < (a * a' : ℕ) := by positivity
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hbRpos) h
  · intro h
    rw [← add_div, hlogmul, h, div_self hlogbne]

/-! ### §4 A multiplicative column quantizes every integral zero-line -/

/-- **Column factorizations are prime-power splits.**  Every factorization `a·a′ = p^k`, including
the degenerate column `k = 0`, has `a = p^i` and `a′ = p^{k−i}` for some `i ≤ k`: divisors of a
prime power are prime powers, and the cofactor is fixed by cancellation. -/
theorem column_quantization {p : ℕ} (hp : p.Prime) {k : ℕ} {a a' : ℕ}
    (ha : a * a' = p ^ k) : ∃ i ≤ k, a = p ^ i ∧ a' = p ^ (k - i) := by
  obtain ⟨i, hik, hai⟩ := (Nat.dvd_prime_pow hp).mp ⟨a', ha.symm⟩
  refine ⟨i, hik, hai, ?_⟩
  have hppos : 0 < p ^ i := pow_pos hp.pos i
  have hsplit : p ^ i * p ^ (k - i) = p ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]
  have hc : p ^ i * a' = p ^ i * p ^ (k - i) := by rw [hsplit, ← hai]; exact ha
  exact Nat.eq_of_mul_eq_mul_left hppos hc

/-- **Quantized zero-lines.**  In the column of frequency `p^k` the prime-power divisor `p^i` sits on
the line `log(p^i)/log(p^k) = i/k`, `log p` cancelling. -/
theorem column_lines_quantized {p : ℕ} (hp : p.Prime) (i k : ℕ) :
    Real.log ((p : ℝ) ^ i) / Real.log ((p : ℝ) ^ k) = (i : ℝ) / (k : ℝ) := by
  have hlp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  rw [Real.log_pow, Real.log_pow, mul_div_mul_right _ _ hlp]

/-- **The critical line is the unique self-dual quantized line.**  For every positive denominator,
`i/k = 1 − i/k ↔ 2i = k`; no separate range condition on `i` is needed. -/
theorem selfdual_iff_half {k i : ℕ} (hk : 0 < k) :
    (i : ℝ) / k = 1 - (i : ℝ) / k ↔ 2 * i = k := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  constructor
  · intro h
    have h2 : (i : ℝ) = (k : ℝ) - i := by
      have hc := congrArg (· * (k : ℝ)) h
      simp only [sub_mul, div_mul_cancel₀ _ hkR, one_mul] at hc
      linarith
    have : (2 * i : ℝ) = (k : ℝ) := by linarith
    exact_mod_cast this
  · intro h
    have hR : (2 * i : ℝ) = (k : ℝ) := by exact_mod_cast h
    field_simp; linarith

/-! ### §5 Composite frequency admits an off-line pair but is not multiplicative -/

/-- The integer-valued arithmetic function supported on `{1, 6}` with values `1` at `1` and `c` at
`6`.  Its base-`6` factor carries an off-line zero when `c ≠ 0`, but the stream is not
multiplicative. -/
def sixCoeff (c : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 1 then 1 else if n = 6 then c else 0, by simp⟩

private theorem sixCoeff_apply (c : ℂ) (n : ℕ) :
    sixCoeff c n = if n = 1 then 1 else if n = 6 then c else 0 := rfl

/-- **The frequency-`6` witness is not multiplicative.**  Multiplicativity across the coprime `2, 3`
would read `sixCoeff c 6 = sixCoeff c 2 · sixCoeff c 3 = 0·0 = 0`, contradicting `c ≠ 0`. -/
theorem sixCoeff_not_multiplicative (c : ℂ) (hc : c ≠ 0) :
    ¬ ArithmeticFunction.IsMultiplicative (sixCoeff c) := by
  intro hmul
  have h := hmul.map_mul_of_coprime (show Nat.Coprime 2 3 by decide)
  rw [show (2 * 3 : ℕ) = 6 from rfl, sixCoeff_apply, sixCoeff_apply, sixCoeff_apply] at h
  norm_num at h
  exact hc h

/-- **The composite off-line pair.**  At frequency `6` the integral mirror pair `2, 3` realizes
`log 2/log 6 + log 3/log 6 = 1` with `log 2/log 6 ≠ 1/2`: an off-critical-line functional-equation
pair, the price paid for dropping multiplicativity. -/
theorem offline_pair_at_six :
    Real.log 2 / Real.log 6 + Real.log 3 / Real.log 6 = 1 ∧
      Real.log 2 / Real.log 6 ≠ 1 / 2 := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog6 : Real.log 6 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  refine ⟨by rw [← add_div, ← h6, div_self hlog6], ?_⟩
  intro heq
  rw [div_eq_iff hlog6, h6] at heq
  have h23 : Real.log 2 = Real.log 3 := by linarith
  have hbad := Real.log_injOn_pos (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3)) h23
  norm_num at hbad

end RHTower
