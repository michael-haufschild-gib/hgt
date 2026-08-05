import GaloisForLFunctions.RHTower.Sieve.LogPhaseBlock

/-!
# Abel summation on a Dirichlet block

Abel's inequality against a decreasing nonneg weight: if every prefix sum of `a` on the
block `[N, M)` is bounded by `P`, the weighted sum obeys `‖∑ w·a‖ ≤ P·w(N)`.  With the
weight `w(n) = 1/n` this converts the dyadic block bound on `∑ n^{-it}` into one on
`∑ n^{-1-it}`, losing exactly a factor `1/N`.
-/

namespace RHTower.Sieve

open Real

/-- Discrete Abel identity on `Ico N M`: weights trade for prefix sums against the
backward difference of the weight, plus a boundary term. -/
theorem sum_weight_mul_eq_abel (a : ℕ → ℂ) (w : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ico N M, ((w n : ℝ) : ℂ) * a n
      = (∑ m ∈ Finset.Ico N M,
          ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n))
        + ((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    have hS : ∑ n ∈ Finset.Ico N (M + 1), a n
        = (∑ n ∈ Finset.Ico N M, a n) + a M := Finset.sum_Ico_succ_top hM a
    rw [Finset.sum_Ico_succ_top hM (fun n => ((w n : ℝ) : ℂ) * a n), ih,
      Finset.sum_Ico_succ_top hM
        (fun m => ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n)),
      hS]
    push_cast
    ring

/-- **Abel's inequality on a block.**  A decreasing nonneg weight against uniformly
bounded prefix sums costs only the leading weight. -/
theorem abel_block_bound (a : ℕ → ℂ) (w : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M)
    (hw0 : 0 ≤ w M) (hanti : ∀ m, N ≤ m → m < M → w (m + 1) ≤ w m)
    (P : ℝ) (hP : ∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ico N m, a n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, ((w n : ℝ) : ℂ) * a n‖ ≤ P * w N := by
  rw [sum_weight_mul_eq_abel a w N M hNM]
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) (hP N le_rfl hNM)
  have hterm : ∀ m ∈ Finset.Ico N M,
      ‖((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖
        ≤ (w m - w (m + 1)) * P := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hdw : 0 ≤ w m - w (m + 1) := sub_nonneg.mpr (hanti m hm.1 hm.2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdw]
    exact mul_le_mul_of_nonneg_left (hP (m + 1) (by omega) (by omega)) hdw
  have htel : ∑ m ∈ Finset.Ico N M, (w m - w (m + 1)) = w N - w M := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h2 := Finset.sum_range_sub' (fun i => w (N + i)) (M - N)
    rw [show N + 0 = N by omega, show N + (M - N) = M by omega] at h2
    exact h2
  calc ‖(∑ m ∈ Finset.Ico N M,
        ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n))
        + ((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖
      ≤ ‖∑ m ∈ Finset.Ico N M,
          ((w m - w (m + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖
        + ‖((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖ := norm_add_le _ _
    _ ≤ (∑ m ∈ Finset.Ico N M, (w m - w (m + 1)) * P) + w M * P := by
        have h1 := le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
        have h2 : ‖((w M : ℝ) : ℂ) * ∑ n ∈ Finset.Ico N M, a n‖ ≤ w M * P := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
          exact mul_le_mul_of_nonneg_left (hP M hNM le_rfl) hw0
        linarith
    _ = (w N - w M) * P + w M * P := by rw [← Finset.sum_mul, htel]
    _ = P * w N := by ring

/-- The weighted Dirichlet block: `‖∑_{N≤n<M} n^{-1-it}‖ ≤ P/N` whenever every prefix of
the unweighted block is bounded by `P`. -/
theorem dirichlet_block_one_bound (t : ℝ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (P : ℝ)
    (hP : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ P * ((N : ℝ))⁻¹ := by
  have hterm : ∀ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))
      = ((((n : ℝ))⁻¹ : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show (-1 - Complex.I * (t : ℂ)) = (-1) + (-(Complex.I * (t : ℂ))) by ring,
      Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hanti : ∀ m, N ≤ m → m < M → ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ((m : ℕ) : ℝ)⁻¹ := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := le_trans hN hm
      exact_mod_cast this
    exact inv_anti₀ hm0 (by push_cast; linarith)
  have hM0 : (0 : ℝ) ≤ ((M : ℕ) : ℝ)⁻¹ := by positivity
  exact abel_block_bound _ (fun n => ((n : ℝ))⁻¹) N M hNM hM0 hanti P hP

/-- **The full weighted dyadic block bound.**  Combining the `k`-th derivative test on
every prefix with Abel's inequality: for `k ≥ 2` with block derivative size
`λ = (t/2π)(k−1)!/(2N)^k ≤ 1` and `N ≤ M ≤ 2N+1`,

  `‖∑_{N≤n<M} n^{-1-it}‖ ≤ 256·((M−N)·(4^k λ)^{1/(2^k−2)} + (M−N)^{1−4/2^k}·λ^{−2/2^k})/N`. -/
theorem dirichlet_block_one_full (t : ℝ) (ht : 0 < t) (k N M : ℕ) (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 256 * (((M - N : ℕ) : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k)))
        * ((N : ℝ))⁻¹ := by
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k
    with hlamdef
  have hπ := Real.pi_pos
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    have h1 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
    have h2 : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k - 1)
    have h3 : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      positivity
    exact div_pos (mul_pos h1 h2) h3
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hβ0 : (0 : ℝ) ≤ 1 - 4 / (2 : ℝ) ^ k := by
    have hDpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h1 : 4 / (2 : ℝ) ^ k ≤ 1 := by
      rw [div_le_one hDpos]; linarith
    linarith
  have hX0 : (0 : ℝ) ≤ ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
    Real.rpow_nonneg (by positivity) _
  have hY0 : (0 : ℝ) ≤ lam ^ (-(2 / (2 : ℝ) ^ k)) := Real.rpow_nonneg hlam0.le _
  set X : ℝ := ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2)) with hXdef
  set Y : ℝ := lam ^ (-(2 / (2 : ℝ) ^ k)) with hYdef
  set P : ℝ := 256 * (((M - N : ℕ) : ℝ) * X
      + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y) with hPdef
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have h1 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) * X := mul_nonneg (Nat.cast_nonneg _) hX0
    have h2 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hY0
    linarith
  have hP : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P := by
    intro m hm1 hm2
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
      exact hP0
    have hL1 : 1 ≤ m - N := by omega
    have hspan : N + (m - N) ≤ 2 * N + 1 := by omega
    have hblock := dirichlet_block_bound t ht k N (m - N) hk hN hL1 hspan hlam1
    rw [Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ i ∈ Finset.range (m - N),
        (((N + i : ℕ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))
          = (((N + i : ℕ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := fun i _ => rfl
    refine le_trans hblock ?_
    rw [hPdef]
    have hLle : ((m - N : ℕ) : ℝ) ≤ ((M - N : ℕ) : ℝ) := by
      have : m - N ≤ M - N := by omega
      exact_mod_cast this
    have h1 : ((m - N : ℕ) : ℝ) * X ≤ ((M - N : ℕ) : ℝ) * X :=
      mul_le_mul_of_nonneg_right hLle hX0
    have h2 : ((m - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
        ≤ ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hLle hβ0
    have h3 : ((m - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y
        ≤ ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y :=
      mul_le_mul_of_nonneg_right h2 hY0
    linarith
  exact dirichlet_block_one_bound t N M hN hNM P hP

end RHTower.Sieve
