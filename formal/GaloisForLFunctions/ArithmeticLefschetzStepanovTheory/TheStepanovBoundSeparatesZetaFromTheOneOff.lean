import GaloisForLFunctions.ArithmeticPositiveDuality.IntegerRoundingPreservesWeightedPrimeCounts

/-!
# The Stepanov bound separates `ζ` from the one-off

The arithmetic Stepanov bound is an upper bound on the degree of the squarefree fixed-point
auxiliary `Π_{p ≤ N} (u_p − 1)`, the prime Lefschetz count `θ(N) = Σ_{p ≤ N} log p`: for `ζ`,
`θ(N) ≤ N + C √N (log N)²` for all large `N` is RH
(`riemannHypothesis_iff_log_length_primeAux_le`). Criterion 3 of §2.9 asks that the bound use
more than the shape of an Euler product. This file tests it on the corpus calibration model.

The **integer-norm one-off** (`ArithmeticPositiveDuality.IntegerNormOneOff`) is an Euler product
`Π_k (1 − q_k^{-s})^{-1}` over integer norms `q_k ≥ 2`, continued to `Re s > ½` with exactly the
zeros `3/5 ± i` there, whose prime count is `θ_F(n) = Σ_{q_k ≤ n} log q_k =
n + n^{3/5} Ω(log n) + O(n^ε)` with `Ω(t) = −2((3/5) cos t + sin t)/((3/5)² + 1)`
(`integer_norm_one_off_with_prime_oscillation`).

* On the progression of heights `log n ∈ [2πj − π/2, 2πj − π/2 + ½]` the oscillation is at least
  `½` (`half_le_oscillation`), and such `n` exist beyond every bound (`exists_nat_log_near`).
* There `θ_F(n) − n ≥ ½ n^{3/5} − O(n^{1/20})`, which beats `C √n (log n)²` for every `C`
  (`sqrt_mul_log_sq_add_lt`).

So **the one-off violates the arithmetic Stepanov bound for every constant**
(`one_off_violates_stepanov_bound`): an Euler product with integer norms and analytic continuation
does not satisfy it. A proof of the bound for `ζ` must use what the one-off lacks — the
functional equation and the rational primes. The bound is one-sided: the real one-off (`γ = 0`,
a real zero at `3/5`) satisfies it (`real_one_off_satisfies_stepanov_bound`), since its oscillation
is negative — as the Stepanov side is blind to real zeros
(`SurfaceOfSpecZ.stepanov_side_blind_to_real_zeros`).
-/

open Real Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- The oscillation of the one-off at `γ = 1` is at least `½` just above `2πj − π/2`. -/
theorem half_le_oscillation (j : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    1 / 2 ≤ -2 * ((3 / 5 : ℝ) * Real.cos (1 * (u - π / 2 + j * (2 * π))) +
      1 * Real.sin (1 * (u - π / 2 + j * (2 * π)))) / ((3 / 5 : ℝ) ^ 2 + 1 ^ 2) := by
  simp only [one_mul, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi,
    Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  have hs : Real.sin u ≤ 1 / 2 := (Real.sin_le hu0).trans hu1
  have hc : 7 / 8 ≤ Real.cos u := by
    have := Real.one_sub_sq_div_two_le_cos (x := u)
    nlinarith
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- Integers whose logarithm lies just above `2πj − π/2`, beyond every bound. -/
theorem exists_nat_log_near (B : ℝ) :
    ∃ n : ℕ, B ≤ n ∧ 1 ≤ n ∧ ∃ j : ℕ, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 / 2 ∧
      Real.log n = u - π / 2 + j * (2 * π) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ((max B 1 + π / 2) / (2 * π) + 1)
  set t : ℝ := -(π / 2) + j * (2 * π)
  have hpi := Real.pi_gt_three
  have ht : max B 1 ≤ t := by
    have h2 : (max B 1 + π / 2) / (2 * π) < j := by linarith
    rw [div_lt_iff₀ (by positivity)] at h2
    simp only [t]; linarith
  have ht1 : 1 ≤ t := (le_max_right B 1).trans ht
  set n : ℕ := ⌈Real.exp t⌉₊
  have hexp : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hn1 : Real.exp t ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < Real.exp t + 1 := Nat.ceil_lt_add_one (Real.exp_pos t).le
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos t) hn1
  refine ⟨n, by linarith [le_max_left B 1], by exact_mod_cast (show (1 : ℝ) ≤ n by linarith),
    j, Real.log n - t, ?_, ?_, by simp only [t]; ring⟩
  · rw [sub_nonneg, ← Real.exp_le_exp, Real.exp_log hnpos]; exact hn1
  · have hle : Real.log n ≤ Real.log (Real.exp t + 1) :=
      Real.log_le_log hnpos hn2.le
    have hsplit : Real.log (Real.exp t + 1) = t + Real.log (1 + Real.exp (-t)) := by
      rw [show Real.exp t + 1 = Real.exp t * (1 + Real.exp (-t)) by
        rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero],
        Real.log_mul (Real.exp_pos t).ne' (by positivity), Real.log_exp]
    have hsmall : Real.log (1 + Real.exp (-t)) ≤ Real.exp (-t) := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-t) by positivity)
      linarith
    have hexpneg : Real.exp (-t) ≤ 1 / 2 := by
      have : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h1 : Real.exp (-1) < 1 / 2 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      linarith
    linarith

/-- `C √x (log x)² + C₁ x^{1/20} < ½ x^{3/5}` once `x^{1/20} > 2(1600|C| + C₁)`. -/
theorem sqrt_mul_log_sq_add_lt {x C C₁ : ℝ} (hx : 1 ≤ x) (hC₁ : 0 ≤ C₁)
    (hlarge : 2 * (1600 * |C| + C₁) < x ^ (1 / 20 : ℝ)) :
    C * Real.sqrt x * Real.log x ^ 2 + C₁ * x ^ (1 / 20 : ℝ) < 1 / 2 * x ^ (3 / 5 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ 40 * x ^ (1 / 40 : ℝ) := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 40 by norm_num)
    linarith
  have hlog2 : Real.log x ^ 2 ≤ 1600 * x ^ (1 / 20 : ℝ) := by
    have h := pow_le_pow_left₀ hlog0 hlog 2
    rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 40 : ℝ)), ← Real.rpow_mul hx0.le] at h
    norm_num at h ⊢
    linarith
  have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hsplit : x ^ (3 / 5 : ℝ) = x ^ (11 / 20 : ℝ) * x ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hhalf : x ^ (1 / 2 : ℝ) * x ^ (1 / 20 : ℝ) = x ^ (11 / 20 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hsmall : x ^ (1 / 20 : ℝ) ≤ x ^ (11 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hpos : 0 < x ^ (11 / 20 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  have h1 : C * Real.sqrt x * Real.log x ^ 2 ≤ 1600 * |C| * x ^ (11 / 20 : ℝ) := by
    calc C * Real.sqrt x * Real.log x ^ 2 ≤ |C| * Real.sqrt x * Real.log x ^ 2 := by
          gcongr
          · exact le_abs_self C
      _ ≤ |C| * x ^ (1 / 2 : ℝ) * (1600 * x ^ (1 / 20 : ℝ)) := by
          rw [hsqrt]; gcongr
      _ = 1600 * |C| * x ^ (11 / 20 : ℝ) := by rw [← hhalf]; ring
  have h2 : C₁ * x ^ (1 / 20 : ℝ) ≤ C₁ * x ^ (11 / 20 : ℝ) := mul_le_mul_of_nonneg_left hsmall hC₁
  have h3 : (1600 * |C| + C₁) * x ^ (11 / 20 : ℝ) < 1 / 2 * x ^ (3 / 5 : ℝ) := by
    rw [hsplit]
    nlinarith
  nlinarith

/-- **The one-off violates the arithmetic Stepanov bound.** There is an Euler product over integer
norms `q_k ≥ 2`, continued to `Re s > ½` with exactly the zeros `3/5 ± i` there, whose prime count
`θ_F(n) = Σ_{q_k ≤ n} log q_k` exceeds `n + C √n (log n)²` at arbitrarily large `n`, for every `C`. -/
theorem one_off_violates_stepanov_bound :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - Complex.exp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + Complex.I, (3 / 5 : ℂ) - Complex.I} ∧
      ∀ C : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
        (n : ℝ) + C * Real.sqrt n * Real.log n ^ 2 <
          ∑' k, if q k ≤ n then Real.log (q k) else 0 := by
  obtain ⟨q, hq, F, Ω, hprod, hdiff, hzeros, hΩ, -, hbound⟩ :=
    ArithmeticPositiveDuality.IntegerNormOneOff.integer_norm_one_off_with_prime_oscillation 1
  refine ⟨q, hq, F, hprod, hdiff, by simpa using hzeros, fun C N₀ => ?_⟩
  obtain ⟨C₁, hC₁, hC₁b⟩ := hbound (1 / 20) (by norm_num)
  set K : ℝ := 2 * (1600 * |C| + C₁)
  obtain ⟨n, hnB, hn1, j, u, hu0, hu1, hlog⟩ := exists_nat_log_near (max N₀ (K ^ 20 + 1))
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨n, by exact_mod_cast (le_max_left _ _).trans hnB, ?_⟩
  have hΩn : 1 / 2 ≤ Ω (Real.log n) := by
    rw [hΩ, hlog]
    exact half_le_oscillation j hu0 hu1
  have hb := hC₁b n hn1
  have hrpow : ∀ a : ℝ, Real.exp (a * Real.log n) = (n : ℝ) ^ a := fun a => by
    rw [Real.rpow_def_of_pos hn0, mul_comm]
  rw [hrpow, hrpow] at hb
  have hK : K < (n : ℝ) ^ (1 / 20 : ℝ) := by
    have hK0 : K ^ 20 < n := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hnB)
    by_cases hKneg : K < 0
    · exact lt_of_lt_of_le hKneg (Real.rpow_nonneg hn0.le _)
    push Not at hKneg
    have := Real.rpow_lt_rpow (pow_nonneg hKneg 20) hK0 (show (0 : ℝ) < ((20 : ℕ) : ℝ)⁻¹ by norm_num)
    rw [Real.pow_rpow_inv_natCast hKneg (by norm_num)] at this
    norm_num at this ⊢
    exact this
  have hkey := sqrt_mul_log_sq_add_lt (C := C) hn1r hC₁.le hK
  have hpow0 : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_nonneg hn0.le _
  have hosc : 1 / 2 * (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) * Ω (Real.log n) := by
    nlinarith
  have habs := (abs_le.mp hb).1
  linarith

/-- **The bound is blind to a real zero.** The real one-off, with the single zero `3/5` in
`Re s > ½`, satisfies `θ_F(n) ≤ n + C √n (log n)²` for all `n ≥ 3`. -/
theorem real_one_off_satisfies_stepanov_bound :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - Complex.exp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} = {(3 / 5 : ℂ)} ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (∑' k, if q k ≤ n then Real.log (q k) else 0) ≤
          (n : ℝ) + C * Real.sqrt n * Real.log n ^ 2 := by
  obtain ⟨q, hq, F, Ω, hprod, hdiff, hzeros, hΩ, -, hbound⟩ :=
    ArithmeticPositiveDuality.IntegerNormOneOff.integer_norm_one_off_with_prime_oscillation 0
  refine ⟨q, hq, F, hprod, hdiff, by simpa using hzeros, ?_⟩
  obtain ⟨C₁, hC₁, hC₁b⟩ := hbound (1 / 20) (by norm_num)
  refine ⟨C₁, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hb := hC₁b n hn1
  have hΩn : Ω (Real.log n) = -(10 / 3) := by rw [hΩ]; norm_num
  have hrpow : ∀ a : ℝ, Real.exp (a * Real.log n) = (n : ℝ) ^ a := fun a => by
    rw [Real.rpow_def_of_pos hn0, mul_comm]
  rw [hrpow, hrpow, hΩn] at hb
  have hpow0 : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_nonneg hn0.le _
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    linarith [Real.exp_one_lt_d9]
  have hsmall : (n : ℝ) ^ (1 / 20 : ℝ) ≤ Real.sqrt n * Real.log n ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    have h1 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
    have h3 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
    nlinarith
  have habs := (abs_le.mp hb).2
  have : C₁ * (n : ℝ) ^ (1 / 20 : ℝ) ≤ C₁ * (Real.sqrt n * Real.log n ^ 2) :=
    mul_le_mul_of_nonneg_left hsmall hC₁.le
  nlinarith

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
