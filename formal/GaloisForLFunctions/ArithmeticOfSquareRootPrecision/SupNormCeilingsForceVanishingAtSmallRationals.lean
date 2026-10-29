import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityExponentIsTheZeroWidth

/-!
# Sup-norm ceilings force vanishing at small rationals

The Siegel half asks for integer polynomials with tiny positive Nair integral. The classical way to
certify smallness is a **sup-norm ceiling**: `0 < ∫₀¹ P ≤ sup_{[0,1]} |P|`. Integrality then acts a
second time, at rational points.

* **Integrality at rationals** (`exists_int_eq_pow_mul_aeval`): `b^n P(a/b) ∈ ℤ` for `deg P ≤ n`; so
  `P(a/b) = 0` or `|P(a/b)| ≥ b^{−n}` (`aeval_eq_zero_or_le_abs`).
* **Forced vanishing** (`aeval_eq_zero_of_sup_lt`): a sup-norm ceiling below `b^{−n}` on `[0, 1]`
  forces `P(a/b) = 0` at every `a/b ∈ [0, 1]`.
* **Precise certificates are Stepanov-like** (`eventually_vanish_of_supCeiling`): for every precision
  `θ < 1`, once `n` is large every integer polynomial of degree `≤ n` with
  `sup_{[0,1]} |P| ≤ e^{−(n+1) + C (n+1)^θ}` vanishes at `0`, `½` and `1`. A sup-norm certificate
  for a zero-free strip must vanish at the rational points of height `2`, as a Stepanov auxiliary
  vanishes at the rational points of a curve.

What a sup-norm ceiling can reach is the integer Chebyshev problem on `[0, 1]`; the vanishing law
is its first structural constraint.
-/

noncomputable section

open Real Finset Polynomial Filter

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- **Integrality at rationals**: `b^n P(a/b) ∈ ℤ` for `deg P ≤ n`, `b ≥ 1`. -/
theorem exists_int_eq_pow_mul_aeval (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n) (a : ℤ) {b : ℕ}
    (hb : 0 < b) : ∃ z : ℤ, (b : ℝ) ^ n * aeval ((a : ℝ) / b) P = z := by
  refine ⟨∑ i ∈ range (n + 1), P.coeff i * a ^ i * (b : ℤ) ^ (n - i), ?_⟩
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP), mul_sum]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [zsmul_eq_mul, div_pow, ← Nat.sub_add_cancel hi', pow_add]
  field_simp
  rw [Nat.sub_add_cancel hi']
  ring

/-- `P(a/b) = 0` or `|P(a/b)| ≥ b^{−n}`. -/
theorem aeval_eq_zero_or_le_abs (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n) (a : ℤ) {b : ℕ}
    (hb : 0 < b) : aeval ((a : ℝ) / b) P = 0 ∨ 1 / (b : ℝ) ^ n ≤ |aeval ((a : ℝ) / b) P| := by
  obtain ⟨z, hz⟩ := exists_int_eq_pow_mul_aeval P hP a hb
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := by have : (0 : ℝ) < b := by exact_mod_cast hb; positivity
  rcases eq_or_ne z 0 with rfl | hz0
  · left
    simpa [hbn.ne'] using hz
  · right
    have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    rw [div_le_iff₀ hbn, ← abs_of_pos hbn, ← abs_mul, abs_of_pos hbn, mul_comm, hz]
    exact h1

/-- **Forced vanishing**: a sup-norm ceiling below `b^{−n}` on `[0, 1]` forces `P(a/b) = 0` at every
`a/b ∈ [0, 1]`. -/
theorem aeval_eq_zero_of_sup_lt (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n) {a : ℤ} {b : ℕ}
    (hb : 0 < b) (ha : (a : ℝ) / b ∈ Set.Icc (0 : ℝ) 1)
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |aeval x P| < 1 / (b : ℝ) ^ n) :
    aeval ((a : ℝ) / b) P = 0 :=
  (aeval_eq_zero_or_le_abs P hP a hb).resolve_right fun h => lt_irrefl _ (lt_of_le_of_lt h (hsup _ ha))

/-- A sup-norm ceiling below `2^{−n}` forces vanishing at `0`, `½` and `1`. -/
theorem vanish_of_sup_lt_two_pow (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n)
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |aeval x P| < 1 / (2 : ℝ) ^ n) :
    aeval (0 : ℝ) P = 0 ∧ aeval (1 / 2 : ℝ) P = 0 ∧ aeval (1 : ℝ) P = 0 := by
  have h2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |aeval x P| < 1 / ((1 : ℕ) : ℝ) ^ n := fun x hx =>
    lt_of_lt_of_le (hsup x hx) (by
      rw [Nat.cast_one, one_pow, div_one]
      exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity))
  have h0 := aeval_eq_zero_of_sup_lt P hP (a := 0) (b := 1) one_pos (by norm_num) h2
  have h1 := aeval_eq_zero_of_sup_lt P hP (a := 1) (b := 1) one_pos (by norm_num) h2
  have hh := aeval_eq_zero_of_sup_lt P hP (a := 1) (b := 2) two_pos (by norm_num)
    (by exact_mod_cast hsup)
  refine ⟨by simpa using h0, by simpa using hh, by simpa using h1⟩

/-- **Precise sup-norm certificates are Stepanov-like.** For every precision `θ < 1` and constant
`C`, for all large `n` every integer polynomial of degree `≤ n` with
`sup_{[0,1]} |P| ≤ e^{−(n+1) + C (n+1)^θ}` vanishes at `0`, `½` and `1`. -/
theorem eventually_vanish_of_supCeiling {θ : ℝ} (hθ : θ < 1) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ℤ[X], P.natDegree ≤ n →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |aeval x P| ≤ exp (-((n + 1 : ℕ) : ℝ) + C * ((n + 1 : ℕ) : ℝ) ^ θ)) →
        aeval (0 : ℝ) P = 0 ∧ aeval (1 / 2 : ℝ) P = 0 ∧ aeval (1 : ℝ) P = 0 := by
  -- eventually `C N^θ < (1 − log 2) N − log 2`, so `e^{−N + C N^θ} < 2^{−(N − 1)}`
  have hl : 0 < 1 - Real.log 2 := by
    have := Real.log_two_lt_d9; linarith
  have hreal : ∀ᶠ N : ℝ in atTop, C * N ^ θ < (1 - Real.log 2) * N - Real.log 2 := by
    have h1 := eventually_mul_rpow_lt_rpow (θ := θ) (b := 1) hθ (2 * C / (1 - Real.log 2))
    filter_upwards [h1, eventually_ge_atTop ((2 * Real.log 2 + 2) / (1 - Real.log 2)),
      eventually_gt_atTop (0 : ℝ)] with N hN hN2 hN0
    rw [Real.rpow_one] at hN
    rw [div_le_iff₀ hl] at hN2
    have he : C * N ^ θ = (1 - Real.log 2) / 2 * (2 * C / (1 - Real.log 2) * N ^ θ) := by
      field_simp
    have hlt := mul_lt_mul_of_pos_left hN (by positivity : 0 < (1 - Real.log 2) / 2)
    rw [he]
    linarith
  filter_upwards [tendsto_succ_cast_atTop.eventually hreal] with n hn P hP hsup
  refine vanish_of_sup_lt_two_pow P hP fun x hx => lt_of_le_of_lt (hsup x hx) ?_
  rw [one_div, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), ← Real.exp_neg, Real.exp_lt_exp,
    Real.log_pow]
  push_cast at hn ⊢
  linarith

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
