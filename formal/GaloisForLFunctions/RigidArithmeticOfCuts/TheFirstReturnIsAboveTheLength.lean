import GaloisForLFunctions.RigidArithmeticOfCuts.ZerosOfADirichletPolynomialRecurEffectively

/-!
# The first return is above the length

Effective Kronecker places a simultaneous return of the phases `n^{-iτ}`, `n ≤ N`, below a height exponential in `N`. How low can it be? It cannot lie below
the length.

**Theorem** (`exists_phase_far`). For `2/log N ≤ τ ≤ N − 1`, some `n ≤ N` has `‖n^{-iτ} − 1‖ ≥ 1/8`.

Near `τ`, consecutive integers `n, n + 1` differ in phase by `τ log(1 + 1/n) ≈ 1`, which is not near `2πℤ`. Below `1`, a single `n ≈ e^{1/τ}` has phase near `1`.

Through primes (`no_prime_return`), phases of composites accumulate at most `Ω(n) ≤ log₂ N` times the prime error, so a return of the primes up to `N` within
`δ < 1/(8 log₂ N)` has `τ < 2/log N` or `τ > N − 1`. Together with effective Kronecker, the first nontrivial return lies between `N` and an exponential in `N`.

This is the height constraint on transport: a head of length `N` can only move a zero to a height above `N`.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The phase as an exponential. -/
theorem phase_eq_exp (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    phase τ n = Complex.exp (I * ((-(τ * Real.log n) : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [phase, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hn0.le]
  congr 1
  push_cast
  ring

/-- `‖e^{ix} − 1‖ ≥ (3/4) x` on `0 < x ≤ 2`. -/
private lemma le_norm_exp_sub_one {x : ℝ} (h0 : 0 < x) (h2 : x ≤ 2) :
    3 / 4 * x ≤ ‖Complex.exp (I * (x : ℂ)) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hx0 : 0 < x / 2 := by linarith
  have hx1 : x / 2 ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx0
  have hcube : (x / 2) ^ 3 ≤ x / 2 := by
    have : (x / 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  refine le_trans ?_ (le_abs_self _)
  linarith

/-- The same for the negative exponent. -/
private lemma le_norm_exp_neg_sub_one {x : ℝ} (h0 : 0 < x) (h2 : x ≤ 2) :
    3 / 4 * x ≤ ‖Complex.exp (I * ((-x : ℝ) : ℂ)) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hx0 : 0 < x / 2 := by linarith
  have hx1 : x / 2 ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx0
  have hcube : (x / 2) ^ 3 ≤ x / 2 := by
    have : (x / 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h3 : -x / 2 = -(x / 2) := by ring
  rw [h3, Real.sin_neg, mul_neg, abs_neg]
  refine le_trans ?_ (le_abs_self _)
  linarith

/-- **Middle heights.** For `1 ≤ τ ≤ N − 1`, consecutive integers near `τ` cannot both have returned. -/
theorem exists_phase_far_of_mid {N : ℕ} {τ : ℝ} (h1 : 1 ≤ τ) (h2 : τ + 1 ≤ N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ 1 / 8 ≤ ‖phase τ n - 1‖ := by
  set n : ℕ := ⌈τ⌉₊ with hn
  have hτn : τ ≤ n := Nat.le_ceil τ
  have hnτ : (n : ℝ) < τ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hnN : n + 1 ≤ N := by
    have : (n : ℝ) < N := by linarith
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set θ : ℝ := τ * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) with hθ
  have hlogup : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div hn1R.ne' hnR.ne']
    have h3 := Real.log_le_sub_one_of_pos (div_pos hn1R hnR)
    have h4 : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / n := by
      push_cast
      field_simp
      ring
    linarith
  have hloglo : 1 / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
    rw [← Real.log_div hn1R.ne' hnR.ne']
    have h3 := Real.one_sub_inv_le_log_of_pos (div_pos hn1R hnR)
    have h4 : 1 - (((n + 1 : ℕ) : ℝ) / n)⁻¹ = 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    linarith
  have hτ0 : 0 < τ := by linarith
  have hθ1 : θ ≤ 1 := by
    have h3 : τ * (1 / (n : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hnR]
      exact hτn
    exact (mul_le_mul_of_nonneg_left hlogup hτ0.le).trans h3
  have hθ3 : 1 / 3 ≤ θ := by
    have h3 : 1 / 3 ≤ τ * (1 / ((n + 1 : ℕ) : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hn1R]
      push_cast
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_left hloglo hτ0.le)
  have hθpos : 0 < θ := by linarith
  by_contra hno
  push Not at hno
  have ha := hno n hn1 (by omega)
  have hb := hno (n + 1) (by omega) hnN
  have hval : phase τ (n + 1) = phase τ n * Complex.exp (I * ((-θ : ℝ) : ℂ)) := by
    rw [phase_eq_exp τ hn1, phase_eq_exp τ (by omega), ← Complex.exp_add]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hunit : ‖phase τ n‖ = 1 := norm_phase τ (by omega)
  have hdiff : ‖phase τ (n + 1) - phase τ n‖ = ‖Complex.exp (I * ((-θ : ℝ) : ℂ)) - 1‖ := by
    have h3 : phase τ (n + 1) - phase τ n = phase τ n * (Complex.exp (I * ((-θ : ℝ) : ℂ)) - 1) := by
      rw [hval]
      ring
    rw [h3, norm_mul, hunit, one_mul]
  have hlow := le_norm_exp_neg_sub_one hθpos (by linarith)
  have htri : ‖phase τ (n + 1) - phase τ n‖ ≤ ‖phase τ (n + 1) - 1‖ + ‖phase τ n - 1‖ := by
    have h3 : phase τ (n + 1) - phase τ n = (phase τ (n + 1) - 1) - (phase τ n - 1) := by ring
    rw [h3]
    exact norm_sub_le _ _
  rw [hdiff] at htri
  linarith

/-- **Low heights.** For `2/log N ≤ τ ≤ 1`, an integer near `e^{1/τ}` has phase near `1` radian. -/
theorem exists_phase_far_of_low {N : ℕ} {τ : ℝ} (h0 : 0 < τ) (h1 : τ ≤ 1) (hτ : 2 ≤ τ * Real.log N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ 1 / 8 ≤ ‖phase τ n - 1‖ := by
  have hNpos : (0 : ℝ) < N := by
    by_contra hneg
    have h2 : (N : ℝ) = 0 := le_antisymm (not_lt.mp hneg) (Nat.cast_nonneg N)
    rw [h2, Real.log_zero, mul_zero] at hτ
    norm_num at hτ
  have hexp1 : (1 : ℝ) ≤ Real.exp (1 / τ) := Real.one_le_exp (by positivity)
  set n : ℕ := ⌈Real.exp (1 / τ)⌉₊ with hn
  have hle : Real.exp (1 / τ) ≤ n := Nat.le_ceil _
  have hlt : (n : ℝ) < Real.exp (1 / τ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnR : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hnR
  have hlogN : 2 / τ ≤ Real.log N := by
    rw [div_le_iff₀ h0]
    linarith
  have hNbig : Real.exp (2 / τ) ≤ N := by
    have := Real.exp_le_exp.mpr hlogN
    rwa [Real.exp_log hNpos] at this
  have hsq : Real.exp (2 / τ) = Real.exp (1 / τ) * Real.exp (1 / τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp2 : (2 : ℝ) ≤ Real.exp (1 / τ) := by
    have h3 : (1 : ℝ) ≤ 1 / τ := by
      rw [le_div_iff₀ h0]
      linarith
    have h4 := Real.add_one_le_exp (1 / τ)
    linarith
  have hnN : n ≤ N := by
    have h3 : (n : ℝ) ≤ N := by nlinarith
    exact_mod_cast h3
  refine ⟨n, hn1, hnN, ?_⟩
  set x : ℝ := τ * Real.log n with hx
  have hx1 : 1 ≤ x := by
    have h3 : 1 / τ ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos _) hle
      rwa [Real.log_exp] at this
    have h4 := mul_le_mul_of_nonneg_left h3 h0.le
    rw [mul_one_div, div_self h0.ne'] at h4
    exact h4
  have hx2 : x ≤ 2 := by
    have h3 : (n : ℝ) ≤ 2 * Real.exp (1 / τ) := by linarith
    have h4 : Real.log n ≤ Real.log 2 + 1 / τ := by
      have := Real.log_le_log hnR h3
      rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    have h5 := mul_le_mul_of_nonneg_left h4 h0.le
    have h6 : τ * (Real.log 2 + 1 / τ) = τ * Real.log 2 + 1 := by
      field_simp
    rw [h6] at h5
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith
    have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  rw [phase_eq_exp τ hn1, ← hx]
  have := le_norm_exp_neg_sub_one (x := x) (by linarith) hx2
  linarith

/-- **No return below the length.** For `2/log N ≤ τ ≤ N − 1`, some `n ≤ N` has `‖n^{-iτ} − 1‖ ≥ 1/8`. -/
theorem exists_phase_far {N : ℕ} {τ : ℝ} (h0 : 0 < τ) (hlow : 2 ≤ τ * Real.log N) (hhigh : τ + 1 ≤ N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ 1 / 8 ≤ ‖phase τ n - 1‖ := by
  rcases le_total τ 1 with h1 | h1
  · exact exists_phase_far_of_low h0 h1 hlow
  · exact exists_phase_far_of_mid h1 hhigh

/-- `2^{Ω(n)} ≤ n`. -/
theorem two_pow_cardFactors_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ ArithmeticFunction.cardFactors n ≤ n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd hn (by norm_num)
  | one => simp
  | prime p hp =>
    rw [ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
    exact hp.two_le
  | mul a b ha hb =>
    have ha0 : 1 ≤ a := Nat.pos_of_mul_pos_right hn
    have hb0 : 1 ≤ b := Nat.pos_of_mul_pos_left hn
    rw [ArithmeticFunction.cardFactors_mul (by omega) (by omega), pow_add]
    exact Nat.mul_le_mul (ha ha0) (hb hb0)

/-- **No prime return below the length.** A height at which all primes up to `N` return within `δ`, with `δ log₂ N < 1/8`, lies below `2/log N` or above
`N − 1`. -/
theorem no_prime_return {N : ℕ} {τ δ : ℝ} (hδ : ((Nat.log 2 N : ℕ) : ℝ) * δ < 1 / 8) (hδ0 : 0 ≤ δ)
    (hret : ∀ p : ℕ, p.Prime → p ≤ N → ‖phase τ p - 1‖ ≤ δ) (h0 : 0 < τ) (hlow : 2 ≤ τ * Real.log N)
    (hhigh : τ + 1 ≤ N) : False := by
  obtain ⟨n, hn1, hnN, hfar⟩ := exists_phase_far h0 hlow hhigh
  have hphase := norm_phase_sub_one_le (τ := τ) (δ := δ) (n := n) hn1 fun p hp hd =>
    hret p hp ((Nat.le_of_dvd (by omega) hd).trans hnN)
  have hΩ : ArithmeticFunction.cardFactors n ≤ Nat.log 2 N := by
    refine Nat.le_log_of_pow_le (by norm_num) ((two_pow_cardFactors_le hn1).trans hnN)
  have hΩR : ((ArithmeticFunction.cardFactors n : ℕ) : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := by exact_mod_cast hΩ
  have := mul_le_mul_of_nonneg_right hΩR hδ0
  linarith

end GaloisForLFunctions.RigidArithmeticOfCuts
