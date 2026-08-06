import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAdmissible

/-!
# The window in which an order saves a power

Both terms of `dirichlet_block_bound_clean` are below `M^{1−ρ}` (with `M = 2N` the block's scale)
exactly on a window of heights:

```text
M^{k − 2 + ρ·2^k/2}  ≤  T  ≤  M^{k − ρ(2^k − 2)} / (4k)^k .
```

The lower end is what the second term needs — the height must be large enough that dividing by it
beats the `M^k` it carries — and the upper end is what the first needs.  The window is non-empty
for `ρ ≍ 2^{−k}`, and it pins the order at `k ≍ log T / log M`.
-/

namespace RHTower.Sieve

/-- **The second term saves a power once the height is past the window's lower end.** -/
theorem block_term_two_le {L M T rho : ℝ} {k : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M) (hT0 : 0 < T)
    (hL0 : 0 ≤ L) (hL : L ≤ M)
    (hTlow : M ^ ((k : ℝ) - 2 + rho * (2 : ℝ) ^ k / 2) ≤ T) :
    L ^ (1 - 4 / (2 : ℝ) ^ k) * (M ^ k / T) ^ (2 / (2 : ℝ) ^ k) ≤ M ^ (1 - rho) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hKge : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have he1 : (0 : ℝ) ≤ 1 - 4 / (2 : ℝ) ^ k := by
    have : 4 / (2 : ℝ) ^ k ≤ 1 := by
      rw [div_le_one hK0]; linarith
    linarith
  have he2 : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ k := by positivity
  -- the length factor
  have h1 : L ^ (1 - 4 / (2 : ℝ) ^ k) ≤ M ^ (1 - 4 / (2 : ℝ) ^ k) :=
    Real.rpow_le_rpow hL0 hL he1
  -- the height factor
  have hsplit : M ^ ((k : ℝ)) = M ^ ((2 : ℝ) - rho * (2 : ℝ) ^ k / 2)
      * M ^ ((k : ℝ) - 2 + rho * (2 : ℝ) ^ k / 2) := by
    rw [← Real.rpow_add hM0]
    congr 1
    ring
  have hdiv : M ^ k / T ≤ M ^ ((2 : ℝ) - rho * (2 : ℝ) ^ k / 2) := by
    rw [div_le_iff₀ hT0, ← Real.rpow_natCast M k, hsplit]
    exact mul_le_mul_of_nonneg_left hTlow (Real.rpow_nonneg hM0.le _)
  have hdiv0 : (0 : ℝ) ≤ M ^ k / T := div_nonneg (by positivity) hT0.le
  have h2 : (M ^ k / T) ^ (2 / (2 : ℝ) ^ k)
      ≤ (M ^ ((2 : ℝ) - rho * (2 : ℝ) ^ k / 2)) ^ (2 / (2 : ℝ) ^ k) :=
    Real.rpow_le_rpow hdiv0 hdiv he2
  -- assemble
  have hcollapse : (M ^ ((2 : ℝ) - rho * (2 : ℝ) ^ k / 2)) ^ (2 / (2 : ℝ) ^ k)
      = M ^ (4 / (2 : ℝ) ^ k - rho) := by
    rw [← Real.rpow_mul hM0.le]
    congr 1
    field_simp
    ring
  have hprod : M ^ (1 - 4 / (2 : ℝ) ^ k) * M ^ (4 / (2 : ℝ) ^ k - rho) = M ^ (1 - rho) := by
    rw [← Real.rpow_add hM0]
    congr 1
    ring
  calc L ^ (1 - 4 / (2 : ℝ) ^ k) * (M ^ k / T) ^ (2 / (2 : ℝ) ^ k)
      ≤ M ^ (1 - 4 / (2 : ℝ) ^ k) * (M ^ ((2 : ℝ) - rho * (2 : ℝ) ^ k / 2)) ^ (2 / (2 : ℝ) ^ k) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hdiv0 _) (Real.rpow_nonneg hM0.le _)
    _ = M ^ (1 - 4 / (2 : ℝ) ^ k) * M ^ (4 / (2 : ℝ) ^ k - rho) := by rw [hcollapse]
    _ = M ^ (1 - rho) := hprod

/-- **The first term saves a power once the height is below the window's upper end.**
`A` carries the order's own weight `(4k)^k`. -/
theorem block_term_one_le {L M T rho A : ℝ} {k : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M)
    (hL0 : 0 ≤ L) (hL : L ≤ M) (hT0 : 0 < T) (hA0 : 0 < A)
    (hTup : T * A ≤ M ^ ((k : ℝ) - rho * ((2 : ℝ) ^ k - 2))) :
    L * (T * A / M ^ k) ^ (1 / ((2 : ℝ) ^ k - 2)) ≤ M ^ (1 - rho) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hKge : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hK2 : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
  have hMk0 : (0 : ℝ) < M ^ k := by positivity
  have he0 : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ k - 2) := by positivity
  -- the base is below `M^{-ρ(K−2)}`
  have hbase : T * A / M ^ k ≤ M ^ (-(rho * ((2 : ℝ) ^ k - 2))) := by
    rw [div_le_iff₀ hMk0, ← Real.rpow_natCast M k, ← Real.rpow_add hM0]
    refine le_trans hTup (le_of_eq ?_)
    congr 1
    ring
  have hbase0 : (0 : ℝ) ≤ T * A / M ^ k := by positivity
  have hpow : (T * A / M ^ k) ^ (1 / ((2 : ℝ) ^ k - 2))
      ≤ (M ^ (-(rho * ((2 : ℝ) ^ k - 2)))) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
    Real.rpow_le_rpow hbase0 hbase he0
  have hcollapse : (M ^ (-(rho * ((2 : ℝ) ^ k - 2)))) ^ (1 / ((2 : ℝ) ^ k - 2))
      = M ^ (-rho) := by
    rw [← Real.rpow_mul hM0.le]
    congr 1
    field_simp
  have hprod : M * M ^ (-rho) = M ^ (1 - rho) := by
    nth_rewrite 1 [show M = M ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hM0]
    congr 1
  calc L * (T * A / M ^ k) ^ (1 / ((2 : ℝ) ^ k - 2))
      ≤ M * (M ^ (-(rho * ((2 : ℝ) ^ k - 2)))) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
        mul_le_mul hL hpow (Real.rpow_nonneg hbase0 _) hM0.le
    _ = M * M ^ (-rho) := by rw [hcollapse]
    _ = M ^ (1 - rho) := hprod

/-- The first term's base against the block's scale `M = 2N`: `(2k/N)^k = (4k)^k/M^k`. -/
theorem block_first_base_rescale {k N : ℕ} (hN : 1 ≤ N) (T : ℝ) :
    T * (2 * (k : ℝ) / (N : ℝ)) ^ k = T * (4 * (k : ℝ)) ^ k / (2 * (N : ℝ)) ^ k := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [div_pow, mul_pow, mul_pow, mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  field_simp

/-- **A block saves a power on the window.**  Both halves of the window put the two terms of
`dirichlet_block_bound_clean` below `M^{1−ρ}`, `M = 2N`. -/
theorem dirichlet_block_saves_power {t : ℝ} (ht : 0 < t) {k N L : ℕ} {rho : ℝ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k)
    (hup : t / (2 * Real.pi) * (4 * (k : ℝ)) ^ k
      ≤ (2 * (N : ℝ)) ^ ((k : ℝ) - rho * ((2 : ℝ) ^ k - 2)))
    (hlow : (2 * (N : ℝ)) ^ ((k : ℝ) - 2 + rho * (2 : ℝ) ^ k / 2) ≤ t / (2 * Real.pi)) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 512 * (2 * (N : ℝ)) ^ (1 - rho) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ 2 * (N : ℝ) := by linarith
  have hLM : (L : ℝ) ≤ 2 * (N : ℝ) := by
    have : L ≤ N + 1 := by omega
    have hLN : (L : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hA0 : (0 : ℝ) < (4 * (k : ℝ)) ^ k := by
    have : (0 : ℝ) < 4 * (k : ℝ) := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    positivity
  have hbase := dirichlet_block_bound_clean ht hk hN hL hspan hcond
  rw [block_first_base_rescale hN] at hbase
  have h1 := block_term_one_le (L := (L : ℝ)) (M := 2 * (N : ℝ)) (T := t / (2 * Real.pi))
    (rho := rho) (A := (4 * (k : ℝ)) ^ k) hk hM1 hL0 hLM hT0 hA0 hup
  have h2 := block_term_two_le (L := (L : ℝ)) (M := 2 * (N : ℝ)) (T := t / (2 * Real.pi))
    (rho := rho) hk hM1 hT0 hL0 hLM hlow
  linarith [hbase, h1, h2]

end RHTower.Sieve
