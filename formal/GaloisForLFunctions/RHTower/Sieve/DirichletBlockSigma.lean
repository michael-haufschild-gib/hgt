import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSchedule

/-!
# The block bound off the line

Abel summation converts a bound on the prefixes of the pure phase sum into a bound on the weighted
sum, and the weight is free: taking `w n = n^(-σ)` instead of `n^(-1)` gives the same estimate with
`N^(-σ)` in place of `N⁻¹`.  Nothing in the derivative test changes, since the phase is the same.

This is what the rectangle version of the estimate needs: the `k`-th derivative test controls
`∑ n^(-it)` on a block, and the weight carries it to `∑ n^(-σ-it)` for any `σ ≥ 0`.
-/

namespace RHTower.Sieve

open Finset

/-- **Weighted block bound off the line.**  For `σ ≥ 0`, a prefix bound `P` on the pure phase sum
gives `‖∑_{N≤n<M} n^(-σ-it)‖ ≤ P · N^(-σ)`. -/
theorem dirichlet_block_sigma_bound {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) (P : ℝ)
    (hP : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ P * ((N : ℝ)) ^ (-σ) := by
  have hterm : ∀ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))
      = ((((n : ℝ)) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := le_trans hN hn.1
    have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hbase : (n : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    rw [show (-(σ : ℂ) - Complex.I * (t : ℂ))
        = (-(σ : ℂ)) + (-(Complex.I * (t : ℂ))) by ring,
      Complex.cpow_add _ _ hn0]
    congr 1
    rw [hbase, show (-(σ : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hn0R.le (-σ)]
  rw [Finset.sum_congr rfl hterm]
  have hanti : ∀ m, N ≤ m → m < M → ((m + 1 : ℕ) : ℝ) ^ (-σ) ≤ ((m : ℕ) : ℝ) ^ (-σ) := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := le_trans hN hm
      exact_mod_cast this
    refine Real.rpow_le_rpow_of_nonpos hm0 ?_ (by linarith)
    push_cast
    linarith
  have hM0 : (0 : ℝ) ≤ ((M : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact abel_block_bound _ (fun n => ((n : ℝ)) ^ (-σ)) N M hNM hM0 hanti P hP


/-! ## The prefix bound, extracted

`dirichlet_block_one_full` establishes this bound inside its own proof.  Stating it separately lets
the same derivative-test input serve any weight; the `σ = 1` case could be refactored to use it. -/

/-- **Prefix bound for the pure phase sum on a dyadic block.** -/
theorem phase_prefix_bound (t : ℝ) (ht : 0 < t) (k N M : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
        ≤ 256 * (((M - N : ℕ) : ℝ)
              * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                  / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
            + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
              * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                  / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k with hlamdef
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
  have hP0 : (0 : ℝ) ≤ 256 * (((M - N : ℕ) : ℝ) * X
      + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y) := by
    have h1 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) * X := mul_nonneg (Nat.cast_nonneg _) hX0
    have h2 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hY0
    linarith
  intro m hm1 hm2
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]
    exact hP0
  have hL1 : 1 ≤ m - N := by omega
  have hspan : N + (m - N) ≤ 2 * N + 1 := by omega
  have hblock := dirichlet_block_bound t ht k N (m - N) hk hN hL1 hspan hlam1
  rw [Finset.sum_Ico_eq_sum_range]
  refine le_trans hblock ?_
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

/-- **Full weighted dyadic block bound off the line.** -/
theorem dirichlet_block_sigma_full {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) (ht : 0 < t) (k N M : ℕ)
    (hk : 2 ≤ k) (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 256 * (((M - N : ℕ) : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k)))
        * ((N : ℝ)) ^ (-σ) :=
  dirichlet_block_sigma_bound hσ t N M hN hNM _ (phase_prefix_bound t ht k N M hk hN hNM hM hlam1)


/-- **Normalised block bound off the line.**  The whole `σ`-dependence is the single factor
`N^(1-σ)` multiplying the bound of the line case. -/
theorem dirichlet_block_sigma_normalized {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) (ht : 0 < t) (k N M : ℕ)
    (hk : 2 ≤ k) (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (N : ℝ) ^ (1 - σ)
        * (512 * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
              / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k))
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k with hlamdef
  have hlam0 : 0 < lam := by
    have h1 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
    have h2 : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k - 1)
    have h3 : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
    rw [hlamdef]
    exact div_pos (mul_pos h1 h2) h3
  set X : ℝ := ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2)) with hXdef
  set Y : ℝ := lam ^ (-(2 / (2 : ℝ) ^ k)) with hYdef
  set β : ℝ := 1 - 4 / (2 : ℝ) ^ k with hβdef
  have hX0 : (0 : ℝ) ≤ X := Real.rpow_nonneg (by positivity) _
  have hY0 : (0 : ℝ) ≤ Y := Real.rpow_nonneg hlam0.le _
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hβ0 : (0 : ℝ) ≤ β := by
    have hDpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h1 : 4 / (2 : ℝ) ^ k ≤ 1 := by rw [div_le_one hDpos]; linarith
    rw [hβdef]; linarith
  have hL : ((M - N : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : (M - N : ℕ) ≤ 2 * N := by omega
    exact_mod_cast this
  have hL0 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNsig : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hN0.le _
  -- the length-absorbing step, before the weight
  have hinner : 256 * (((M - N : ℕ) : ℝ) * X + ((M - N : ℕ) : ℝ) ^ β * Y)
      ≤ (N : ℝ) * (512 * X + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y) := by
    have h1 : 256 * (((M - N : ℕ) : ℝ) * X) ≤ (N : ℝ) * (512 * X) := by
      nlinarith [mul_le_mul_of_nonneg_right hL hX0, hX0, hN0]
    have hpow : ((M - N : ℕ) : ℝ) ^ β ≤ 2 * (N : ℝ) ^ β := by
      have hstep : ((M - N : ℕ) : ℝ) ^ β ≤ (2 * (N : ℝ)) ^ β := Real.rpow_le_rpow hL0 hL hβ0
      have hsplit : (2 * (N : ℝ)) ^ β = (2 : ℝ) ^ β * (N : ℝ) ^ β :=
        Real.mul_rpow (by norm_num) hN0.le
      have htwo : (2 : ℝ) ^ β ≤ 2 := by
        have hb1 : β ≤ 1 := by
          rw [hβdef]
          have : (0 : ℝ) < 4 / (2 : ℝ) ^ k := by positivity
          linarith
        calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1
          _ = 2 := Real.rpow_one 2
      have hNβ : (0 : ℝ) ≤ (N : ℝ) ^ β := Real.rpow_nonneg hN0.le _
      calc ((M - N : ℕ) : ℝ) ^ β ≤ (2 : ℝ) ^ β * (N : ℝ) ^ β := hsplit ▸ hstep
        _ ≤ 2 * (N : ℝ) ^ β := mul_le_mul_of_nonneg_right htwo hNβ
    have hmerge : (N : ℝ) * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) = (N : ℝ) ^ β := by
      nth_rewrite 1 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hN0, hβdef]
      ring_nf
    have h2 : 256 * (((M - N : ℕ) : ℝ) ^ β * Y)
        ≤ (N : ℝ) * (512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y) := by
      have hgoal : (N : ℝ) * (512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y) = 512 * (N : ℝ) ^ β * Y := by
        rw [← hmerge]; ring
      rw [hgoal]
      nlinarith [mul_le_mul_of_nonneg_right hpow hY0, hY0]
    linarith
  refine le_trans (dirichlet_block_sigma_full hσ t ht k N M hk hN hNM hM hlam1) ?_
  have hsplit : (N : ℝ) ^ (1 - σ) = (N : ℝ) * (N : ℝ) ^ (-σ) := by
    nth_rewrite 2 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hN0]
    ring_nf
  have hRHS : (N : ℝ) ^ (1 - σ)
        * (512 * X + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y)
      = ((N : ℝ) * (512 * X + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y)) * (N : ℝ) ^ (-σ) := by
    rw [hsplit]; ring
  rw [hRHS]
  exact mul_le_mul_of_nonneg_right hinner hNsig


/-- **Balanced saving off the line.**  In the saving window the block obeys the same bound as on the
line, times `N^(1-σ)`. -/
theorem dirichlet_block_sigma_saving {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) (ht : 0 < t) (k N M : ℕ)
    (hk : 2 ≤ k) (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1)
    (hlam1 : blockLambda t N k ≤ 1)
    (hhigh : blockLambda t N k ≤ (N : ℝ) ^ (-(1 / 3) : ℝ))
    (hlow : (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ blockLambda t N k) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlam0 : 0 < blockLambda t N k := blockLambda_pos ht hN k
  have hNsig : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg hN0.le _
  have hbracket := block_saving_wide k N hk hN _ hlam0 hhigh hlow
  refine le_trans (dirichlet_block_sigma_normalized hσ t ht k N M hk hN hNM hM hlam1) ?_
  calc (N : ℝ) ^ (1 - σ)
        * (512 * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)))
      ≤ (N : ℝ) ^ (1 - σ) * (2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))) :=
        mul_le_mul_of_nonneg_left hbracket hNsig
    _ = 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) := by ring

/-- **Per-block estimate off the line at the classical scale.** -/
theorem dirichlet_block_sigma_saving_of_small_factorial {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t)
    {N M k₀ : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N + 1) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ (k₀ - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk, hkle, hlowk, hhighk⟩ :=
    exists_blockLambda_in_window ht hN hk₀ (blockLambda_two_ge hN hlow)
      (blockLambda_le_of_small_factorial ht hN (by omega) hfac hhigh)
  have hlam1 : blockLambda t N k ≤ 1 :=
    hhighk.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
  have hmono : (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hpk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k₀ := pow_le_pow_right₀ (by norm_num) hkle
    have hpos : (0 : ℝ) < 3 * (2 : ℝ) ^ k := by positivity
    have hle : 1 / (3 * (2 : ℝ) ^ k₀) ≤ 1 / (3 * (2 : ℝ) ^ k) :=
      one_div_le_one_div_of_le hpos (by linarith)
    linarith
  have hNsig : (0 : ℝ) ≤ 2560 * (N : ℝ) ^ (1 - σ) := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg hN0.le _
    linarith
  refine le_trans
    (dirichlet_block_sigma_saving hσ t ht k N M hk hN hNM hM hlam1 hhighk hlowk) ?_
  exact mul_le_mul_of_nonneg_left hmono hNsig

end RHTower.Sieve
