import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.Sieve.MoebiusFrequencyDistance
import GaloisForLFunctions.RHTower.ZetaVerticalLineBound

/-!
# The prime cosine sum with a quarter of the frequency loss

`Sieve/PrimeCosineSum.sum_cos_div_prime_ge` reaches the one-line through the zero-free strip and
pays `7 log log|t|`, at the price of the strip condition `log⁹|t|/A ≤ log z`.  The three-four-one
inequality applied *directly at the standard abscissa* `σ = 1 + 1/log z` pays instead

    (3/4)·log log z  +  (1/4)·log log|t| ,

with no condition linking `z` and `t`.  Against the harmonic mass `log log z` of the Möbius distance
this leaves `(1/4)(log log z − log log|t|)`, which is a positive proportion of `log log z` for every
frequency with `log|t| ≤ (log z)^{1−c}` — a far larger range than the strip allows.

The three inputs are the three-four-one product inequality, the pole bound `‖ζ(1+x)‖ ≤ 1/x + 2`,
and the vertical-line bound `‖ζ(s)‖ ≤ log|Im s| + 5`.
-/

namespace RHTower.Sieve

open Complex

/-- **The three-four-one lower bound at a free abscissa.** -/
theorem log_norm_riemannZeta_ge_three_four_one {x t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (ht : 2 ≤ |t|) :
    -(3 / 4) * Real.log (1 / x + 2) - (1 / 4) * Real.log (Real.log (2 * |t|) + 5)
      ≤ Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hcast1 : ((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I = 1 + (x : ℂ) + Complex.I * (t : ℂ) := by
    push_cast; ring
  have hprod := norm_zeta_product_ge_one hx0 t
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  -- the three factors
  have hA : ‖riemannZeta (1 + (x : ℂ))‖ ≤ 1 / x + 2 := by
    have h := abs_riemannZeta_one_add_le hx0
    convert h using 3
  have hA0 : (0 : ℝ) ≤ ‖riemannZeta (1 + (x : ℂ))‖ := norm_nonneg _
  have hAle : (0 : ℝ) < 1 / x + 2 := by positivity
  have htabs : (0 : ℝ) < |t| := by linarith
  have h2t : (2 : ℝ) ≤ |2 * t| := by rw [abs_mul]; simp only [abs_two]; linarith
  have hC : ‖riemannZeta (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ))‖ ≤ Real.log (2 * |t|) + 5 := by
    have hre : (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ)).re = 1 + x := by
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    have him : (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ)).im = 2 * t := by
      simp [Complex.add_im, Complex.mul_re, Complex.mul_im]
    have h := norm_riemannZeta_le_log_add (s := 1 + (x : ℂ) + 2 * Complex.I * (t : ℂ))
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact h2t)
    rw [him] at h
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; simp
    rwa [habs] at h
  have hClog : (0 : ℝ) < Real.log (2 * |t|) + 5 := by
    have : (0 : ℝ) ≤ Real.log (2 * |t|) := Real.log_nonneg (by linarith)
    linarith
  have hC0 : (0 : ℝ) ≤ ‖riemannZeta (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ))‖ := norm_nonneg _
  set B : ℝ := ‖riemannZeta (1 + (x : ℂ) + Complex.I * (t : ℂ))‖ with hB
  have hB0 : (0 : ℝ) ≤ B := norm_nonneg _
  -- the product bound
  have hmaj : ‖riemannZeta (1 + (x : ℂ))‖ ^ (3 : ℕ)
        * ‖riemannZeta (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ))‖
      ≤ (1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5) := by
    have h1 : ‖riemannZeta (1 + (x : ℂ))‖ ^ (3 : ℕ) ≤ (1 / x + 2) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hA0 hA 3
    exact mul_le_mul h1 hC hC0 (by positivity)
  have hkey : 1 ≤ (1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5) * B ^ (4 : ℕ) := by
    have hstep : ‖riemannZeta (1 + (x : ℂ))‖ ^ (3 : ℕ) * B ^ (4 : ℕ)
          * ‖riemannZeta (1 + (x : ℂ) + 2 * Complex.I * (t : ℂ))‖
        ≤ (1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5) * B ^ (4 : ℕ) := by
      nlinarith [hmaj, pow_nonneg hB0 4, hA0, hC0, pow_nonneg hA0 3]
    linarith [hprod, hstep]
  have hden : (0 : ℝ) < (1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5) := by positivity
  have hB4 : ((1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5))⁻¹ ≤ B ^ (4 : ℕ) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    calc (1 : ℝ) ≤ (1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5) * B ^ (4 : ℕ) := hkey
      _ = B ^ (4 : ℕ) * ((1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5)) := by ring
  have hB4pos : (0 : ℝ) < B ^ (4 : ℕ) := by
    have hpos : (0 : ℝ) < ((1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5))⁻¹ := by positivity
    linarith
  have hBpos : (0 : ℝ) < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hB4pos; simp at hB4pos
  -- take logarithms
  have hlog := Real.log_le_log (by positivity) hB4
  rw [Real.log_pow] at hlog
  have hval : Real.log (((1 / x + 2) ^ (3 : ℕ) * (Real.log (2 * |t|) + 5))⁻¹)
      = -(3 * Real.log (1 / x + 2)) - Real.log (Real.log (2 * |t|) + 5) := by
    rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hval] at hlog
  rw [hcast1, ← hB]
  push_cast at hlog ⊢
  linarith

/-- **The prime cosine sum at the standard abscissa, with only a quarter of the frequency loss.** -/
theorem exists_sum_cos_div_prime_ge_sharp :
    ∃ C : ℝ, ∀ (z : ℕ) (t : ℝ), 3 ≤ z → 2 ≤ |t| →
      -(3 / 4) * Real.log (Real.log (z : ℝ) + 2)
          - (1 / 4) * Real.log (Real.log (2 * |t|) + 5) - C
        ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  refine ⟨Real.pi ^ (2 : ℕ) / 6
    + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + (1 + Real.log 4), ?_⟩
  intro z t hz ht
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  set x : ℝ := 1 / Real.log (z : ℝ) with hxdef
  have hx0 : (0 : ℝ) < x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one hlogz0]; linarith
  have hinv : 1 / x = Real.log (z : ℝ) := by
    rw [hxdef]; field_simp
  have hσ1 : (1 : ℝ) < 1 + x := by linarith
  have hlogζ := log_norm_riemannZeta_ge_three_four_one hx0 hx1 ht
  rw [hinv] at hlogζ
  have hprime := le_tsum_re_prime_cpow_of_log_le (σ := 1 + x) (t := t) hσ1 hlogζ
  have hxeq : (1 : ℝ) + x = 1 + 1 / Real.log (z : ℝ) := by rw [hxdef]
  rw [hxeq] at hprime
  have hfin := sum_cos_div_prime_ge_of_le hz hprime
  linarith [hfin]

/-- **The Möbius distance with only a quarter of the frequency loss.**  For every frequency the
squared distance is at least `(log log z − log log|t|)/4 − C`, with **no condition linking `z` and
`t`**.  In particular it is a positive proportion of `log log z` for every `|t| ≤ exp((log z)^{1−c})`
— the range the zero-free strip cannot reach. -/
theorem exists_mulDistSqPair_ge_quarter :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ) (z : ℕ) (t : ℝ), 3 ≤ z → 9 ≤ |t| →
      (∀ p ∈ Nat.primesLE z, f p = -1) →
      (1 / 4) * logLog z - (1 / 4) * Real.log (Real.log |t|) - C
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨C₁, hC₁⟩ := exists_sum_cos_div_prime_ge_sharp
  refine ⟨C₁ + mertensSecondLowerConst + (3 / 4) * Real.log 3 + (1 / 4) * Real.log 4, ?_⟩
  intro f z t hz ht hf
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have htabs : (9 : ℝ) ≤ |t| := ht
  have hlogt : (2 : ℝ) ≤ Real.log |t| := by
    have hexp : Real.exp 2 ≤ |t| := by
      have := exp_two_lt_eight
      linarith
    have := Real.log_le_log (Real.exp_pos 2) hexp
    rwa [Real.log_exp] at this
  have hlogt0 : (0 : ℝ) < Real.log |t| := by linarith
  -- the two logarithmic comparisons
  have hlogLog : logLog z = Real.log (Real.log (z : ℝ)) := rfl
  have hzcmp : Real.log (Real.log (z : ℝ) + 2) ≤ Real.log 3 + Real.log (Real.log (z : ℝ)) := by
    have hle : Real.log (z : ℝ) + 2 ≤ 3 * Real.log (z : ℝ) := by linarith
    have h := Real.log_le_log (by linarith) hle
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogz0)] at h
  have htcmp : Real.log (Real.log (2 * |t|) + 5) ≤ Real.log 4 + Real.log (Real.log |t|) := by
    have hsplit : Real.log (2 * |t|) = Real.log 2 + Real.log |t| :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog2pos : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have hle : Real.log (2 * |t|) + 5 ≤ 4 * Real.log |t| := by
      rw [hsplit]; linarith
    have h := Real.log_le_log (by rw [hsplit]; linarith) hle
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogt0)] at h
  -- Mertens and the cosine sum
  have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
    le_mertensS (by omega)
  have hcos := hC₁ z t hz (by linarith)
  rw [mulDistSqPair_neg_one_split hf t, hlogLog] at *
  linarith

end RHTower.Sieve
