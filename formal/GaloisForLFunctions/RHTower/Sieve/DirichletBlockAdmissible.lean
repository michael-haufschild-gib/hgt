import GaloisForLFunctions.RHTower.Sieve.LogPhaseBlock

/-!
# Admissibility of the derivative order

`dirichlet_block_bound` applies at order `k` only when its window parameter

```text
λ = (t/2π)·(k−1)! / (2N)^k
```

is at most one.  Since `(k−1)! ≤ k^k`, that holds as soon as `(t/2π)·k^k ≤ (2N)^k`, i.e. as soon as
the block is past `k·(t/2π)^{1/k}`.  Stating the condition this way removes the factorial and makes
the order `k` a free parameter that an optimisation can move with `N`.
-/

namespace RHTower.Sieve

/-- The factorial in the window parameter is dominated by `k^k`. -/
theorem factorial_pred_le_pow_self {k : ℕ} (hk : 1 ≤ k) :
    ((Nat.factorial (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
  have h1 : Nat.factorial (k - 1) ≤ (k - 1) ^ (k - 1) := Nat.factorial_le_pow (k - 1)
  have h2 : (k - 1) ^ (k - 1) ≤ k ^ (k - 1) := Nat.pow_le_pow_left (by omega) (k - 1)
  have h3 : k ^ (k - 1) ≤ k ^ k := Nat.pow_le_pow_right hk (by omega)
  have h : Nat.factorial (k - 1) ≤ k ^ k := le_trans h1 (le_trans h2 h3)
  exact_mod_cast h

/-- **The window parameter is admissible once the block is past `k·(t/2π)^{1/k}`.** -/
theorem dirichlet_block_lam_le_one {t : ℝ} (ht : 0 < t) {k N : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k) :
    t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1 := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
  rw [div_le_one hden]
  have hfac := factorial_pred_le_pow_self hk
  have hstep := mul_le_mul_of_nonneg_left hfac hT0.le
  linarith [hstep, hcond]

/-- **The block bound at an admissible order.**  The factorial hypothesis of
`dirichlet_block_bound` is replaced by the factorial-free condition. -/
theorem dirichlet_block_bound_of_pow {t : ℝ} (ht : 0 < t) {k N L : ℕ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) :=
  dirichlet_block_bound t ht k N L hk hN hL hspan
    (dirichlet_block_lam_le_one ht (by omega) hN hcond)

/-- **The block bound is monotone in the window parameter**, upwards in the first term and
downwards in the second.  Substituting an upper bound for `λ` in the first and a lower bound in
the second is therefore legitimate, which is what makes the order `k` optimisable: the factorial
can be replaced by `k^k` above and by `1` below. -/
theorem block_terms_mono {L lam lamL lamU : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hL0 : 0 ≤ L) (hlamL0 : 0 < lamL) (hlow : lamL ≤ lam) (hupp : lam ≤ lamU) :
    L * ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
        + L ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(2 / (2 : ℝ) ^ k))
      ≤ L * ((4 : ℝ) ^ k * lamU) ^ (1 / ((2 : ℝ) ^ k - 2))
        + L ^ (1 - 4 / (2 : ℝ) ^ k) * lamL ^ (-(2 / (2 : ℝ) ^ k)) := by
  have hK : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hexp0 : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ k - 2) := by
    refine div_nonneg (by norm_num) ?_
    linarith
  have hneg : -(2 / (2 : ℝ) ^ k) ≤ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ k := by positivity
    linarith
  have hfour : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le hlamL0 hlow
  have hfirst : ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
      ≤ ((4 : ℝ) ^ k * lamU) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
    Real.rpow_le_rpow (mul_nonneg hfour.le hlam0.le) (by nlinarith [hupp, hfour]) hexp0
  have hsecond : lam ^ (-(2 / (2 : ℝ) ^ k)) ≤ lamL ^ (-(2 / (2 : ℝ) ^ k)) :=
    Real.rpow_le_rpow_of_nonpos hlamL0 hlow hneg
  have hLpow : (0 : ℝ) ≤ L ^ (1 - 4 / (2 : ℝ) ^ k) := Real.rpow_nonneg hL0 _
  have h1 := mul_le_mul_of_nonneg_left hfirst hL0
  have h2 := mul_le_mul_of_nonneg_left hsecond hLpow
  linarith [h1, h2]

/-- **The block bound as pure powers.**  Substituting `1 ≤ (k−1)! ≤ k^k` through
`block_terms_mono` removes the factorial entirely: the estimate now depends on the block only
through `N`, `L`, the height `t` and the order `k`, which is what an optimisation over `k` needs. -/
theorem dirichlet_block_bound_powers {t : ℝ} (ht : 0 < t) {k N L : ℕ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (k : ℝ) ^ k / (2 * (N : ℝ)) ^ k))
                ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * 1 / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
  have hfacpos : (1 : ℝ) ≤ ((Nat.factorial (k - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))
  have hfacle := factorial_pred_le_pow_self (k := k) (by omega)
  have hlow : t / (2 * Real.pi) * 1 / (2 * (N : ℝ)) ^ k
      ≤ t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfacpos hT0.le) hden.le
  have hupp : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k
      ≤ t / (2 * Real.pi) * (k : ℝ) ^ k / (2 * (N : ℝ)) ^ k :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfacle hT0.le) hden.le
  have hlamL0 : (0 : ℝ) < t / (2 * Real.pi) * 1 / (2 * (N : ℝ)) ^ k := by
    rw [mul_one]
    exact div_pos hT0 hden
  have hmono := block_terms_mono (L := (L : ℝ)) (k := k) hk (by positivity) hlamL0 hlow hupp
  have hbase := dirichlet_block_bound_of_pow ht hk hN hL hspan hcond
  linarith [hbase, mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 256)]

/-- The first term's base, in lowest terms: `4^k·T·k^k/(2N)^k = T·(2k/N)^k`. -/
theorem block_first_base_eq {T : ℝ} {k N : ℕ} (hN : 1 ≤ N) :
    (4 : ℝ) ^ k * (T * (k : ℝ) ^ k / (2 * (N : ℝ)) ^ k)
      = T * (2 * (k : ℝ) / (N : ℝ)) ^ k := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [div_pow, mul_pow, mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  field_simp

/-- The second term's base, inverted: `(T/(2N)^k)^{-e} = ((2N)^k/T)^e`. -/
theorem block_second_base_eq {T D e : ℝ} (hT : 0 < T) (hD : 0 < D) :
    (T * 1 / D) ^ (-e) = (D / T) ^ e := by
  rw [mul_one, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]

/-- **The block bound in lowest terms.**  Both bases are now single powers, so the exponents
`1/(2^k−2)` and `2/2^k` sit against `(2k/N)^k` and `(2N)^k/T` respectively — the shape an
optimisation over `k` reads off. -/
theorem dirichlet_block_bound_clean {t : ℝ} (ht : 0 < t) {k N L : ℕ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * (t / (2 * Real.pi) * (2 * (k : ℝ) / (N : ℝ)) ^ k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * ((2 * (N : ℝ)) ^ k / (t / (2 * Real.pi))) ^ (2 / (2 : ℝ) ^ k)) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
  have hbase := dirichlet_block_bound_powers ht hk hN hL hspan hcond
  rw [block_first_base_eq (T := t / (2 * Real.pi)) hN,
    block_second_base_eq (T := t / (2 * Real.pi)) (D := (2 * (N : ℝ)) ^ k) hT0 hden] at hbase
  exact hbase

end RHTower.Sieve
