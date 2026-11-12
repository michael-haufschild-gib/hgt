import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma

/-!
# The derivative test for shifted logarithmic phases

`(n+α)^{-it} = e(g_t(n+α))`, `g_t(x) = −(t/2π) log x`, so a run of shifted phases is a run of
`g_t` sampled from the real start point `N + α`.  The `k`-th derivative test
(`Sieve.kth_derivative_test`) takes real start points, and on `[N + α, N + α + L − 1] ⊂ [N, 2N]`
(`N + L ≤ 2N`, `0 ≤ α ≤ 1`) the top derivative of `g_t` is pinned between `λ` and `2^k λ`,
`λ = (t/2π)(k−1)!/(2N)^k`, exactly as for `n^{-it}`:

* `shifted_block_bound`: `‖Σ_{j<L} (N+j+α)^{-it}‖ ≤ 256(L(4^kλ)^{1/(2^k−2)} + L^{1−4/2^k}λ^{−2/2^k})`;
* `shifted_block_sigma_saving_of_small_factorial`: with the weight `(n+α)^{-σ}`, `σ ≥ 0`, a block
  `[N, M)`, `M ≤ 2N`, in the range `8πN^{1/3} ≤ t ≤ 2π 2^{k₀} N^{k₀−1} N^{−1/3}`, `(k₀−1)! ≤ N`, has
  `‖Σ_{N≤n<M} (n+α)^{-σ-it}‖ ≤ 2560 N^{1−σ} N^{−1/(3·2^{k₀})}`.
-/

open Finset RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `x^{-it}` is the phase `e(g_t(x))` for real `x > 0`. -/
theorem ofReal_cpow_neg_I_mul (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * logPhase t x : ℝ) : ℂ) * Complex.I) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
  congr 1
  simp only [logPhase]
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **The derivative test for shifted phases.** For `0 ≤ α ≤ 1`, `k ≥ 2`, `N + L ≤ 2N` and
`λ = (t/2π)(k−1)!/(2N)^k ≤ 1`. -/
theorem shifted_block_bound (t : ℝ) (ht : 0 < t) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (k N L : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ j ∈ Finset.range L, ((((N + j : ℕ) : ℝ) + α : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlam1 ⊢
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial j : ℝ) / (2 * (N : ℝ)) ^ (j + 1)
    with hlamdef
  have hπ := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hN1)
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    have h1 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
    have h2 : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have h3 : (0 : ℝ) < (2 * (N : ℝ)) ^ (j + 1) := by positivity
    exact div_pos (mul_pos h1 h2) h3
  have hgrow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    calc (1 : ℝ) = 2 ^ 0 := by norm_num
      _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ one_le_two (Nat.zero_le _)
  have hlam_eq : lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * ((2 * (N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef, div_eq_mul_inv]
  have hupper_eq : (2 : ℝ) ^ (j + 1) * lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (((N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef]
    field_simp [mul_pow]
    ring
  -- the shifted sample span sits inside the dyadic window
  have hspan_mem : ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
      0 < x ∧ x ∈ Set.Icc ((N : ℝ)) (2 * (N : ℝ)) := by
    intro x hx
    have hL1 : ((L - 1 : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      have : L - 1 + 1 ≤ N := by omega
      exact_mod_cast this
    exact ⟨by linarith [hx.1], by linarith [hx.1], by linarith [hx.2]⟩
  -- rewrite the shifted terms as phases
  have hphase : ∀ i ∈ Finset.range L,
      ((((N + i : ℕ) : ℝ) + α : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
        = Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + α + i) : ℝ) : ℂ) * Complex.I) := by
    intro i _
    have harg : ((N + i : ℕ) : ℝ) + α = (N : ℝ) + α + (i : ℝ) := by push_cast; ring
    rw [harg]
    exact ofReal_cpow_neg_I_mul t (by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith)
  rw [Finset.sum_congr rfl hphase]
  rw [show (4 : ℝ) ^ (j + 1) = ((2 : ℝ) ^ (j + 1)) ^ 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
  rcases Nat.even_or_odd (j + 1) with hev | hodd
  · have hone : ((-1 : ℝ)) ^ (j + 1) = 1 := Even.neg_one_pow hev
    have hchain : ∀ i < j + 1,
        ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        HasDerivAt (logPhaseChain t i) (logPhaseChain t (i + 1) x) x :=
      fun i _ x hx => logPhaseChain_hasDerivAt t i (hspan_mem x hx).1
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        lam ≤ logPhaseChain t (j + 1) x := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hone, one_mul] at hb
      rw [hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        logPhaseChain t (j + 1) x ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hone, one_mul] at hb
      rw [hupper_eq]
      exact hb
    exact kth_derivative_test (j + 1) hk (logPhaseChain t) ((N : ℝ) + α) L hL
      hlam0 hlam1 hgrow1 hchain hlo hhi
  · have hneg : ((-1 : ℝ)) ^ (j + 1) = -1 := Odd.neg_one_pow hodd
    have hchain : ∀ i < j + 1,
        ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        HasDerivAt (fun y => -(logPhaseChain t i y)) (-(logPhaseChain t (i + 1) x)) x :=
      fun i _ x hx => (logPhaseChain_hasDerivAt t i (hspan_mem x hx).1).neg
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        lam ≤ -(logPhaseChain t (j + 1) x) := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hneg, neg_one_mul] at hb
      rw [hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ) + α) ((N : ℝ) + α + ((L - 1 : ℕ) : ℝ)),
        -(logPhaseChain t (j + 1) x) ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hneg, neg_one_mul] at hb
      rw [hupper_eq]
      exact hb
    have hDk := kth_derivative_test (j + 1) hk (fun i y => -(logPhaseChain t i y))
      ((N : ℝ) + α) L hL hlam0 hlam1 hgrow1 hchain hlo hhi
    rw [← norm_phase_sum_neg (logPhase t) ((N : ℝ) + α) L]
    exact hDk

/-- **Prefix bound for the shifted phase sum on a dyadic block** `[N, M)`, `M ≤ 2N`. -/
theorem shifted_phase_prefix_bound (t : ℝ) (ht : 0 < t) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (k N M : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
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
  have hspan : N + (m - N) ≤ 2 * N := by omega
  have hblock := shifted_block_bound t ht hα0 hα1 k N (m - N) hk hN hL1 hspan hlam1
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

/-- **Weighted shifted block.** A prefix bound `P` for `Σ (n+α)^{-it}` gives
`‖Σ_{N≤n<M} (n+α)^{-σ-it}‖ ≤ P (N+α)^{-σ}` for `σ ≥ 0`, `α ≥ 0`. -/
theorem shifted_block_sigma_bound {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) {α : ℝ} (hα0 : 0 ≤ α)
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (P : ℝ)
    (hP : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico N m, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ P * ((N : ℝ) + α) ^ (-σ) := by
  have hpos : ∀ n : ℕ, N ≤ n → (0 : ℝ) < (n : ℝ) + α := by
    intro n hn
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hN hn
    linarith
  have hterm : ∀ n ∈ Finset.Ico N M,
      ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))
        = (((((n : ℝ) + α) ^ (-σ) : ℝ)) : ℂ)
          * ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
    intro n hn
    have hx := hpos n (Finset.mem_Ico.mp hn).1
    have hx0 : ((((n : ℝ) + α : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show (-(σ : ℂ) - Complex.I * (t : ℂ)) = (-(σ : ℂ)) + (-(Complex.I * (t : ℂ))) by ring,
      Complex.cpow_add _ _ hx0]
    congr 1
    rw [show (-(σ : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx.le (-σ)]
  rw [Finset.sum_congr rfl hterm]
  have hanti : ∀ m, N ≤ m → m < M →
      ((m + 1 : ℕ) : ℝ) + α ≤ ((m + 1 : ℕ) : ℝ) + α →
      (((m + 1 : ℕ) : ℝ) + α) ^ (-σ) ≤ ((m : ℝ) + α) ^ (-σ) := by
    intro m hm _ _
    refine Real.rpow_le_rpow_of_nonpos (hpos m hm) ?_ (by linarith)
    push_cast
    linarith
  have hM0 : (0 : ℝ) ≤ ((M : ℝ) + α) ^ (-σ) :=
    Real.rpow_nonneg (by have := Nat.cast_nonneg (α := ℝ) M; linarith) _
  exact abel_block_bound _ (fun n => ((n : ℝ) + α) ^ (-σ)) N M hNM hM0
    (fun m hm hmM => hanti m hm hmM le_rfl) P hP

/-- Absorbing the block length: for `M − N ≤ 2N`,
`256((M−N)X + (M−N)^{1−4/2^k} Y) N^{-σ} ≤ N^{1−σ}(512X + 512 N^{−4/2^k} Y)`. -/
theorem block_length_absorb {σ : ℝ} {k N M : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hL : M - N ≤ 2 * N) {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) :
    256 * (((M - N : ℕ) : ℝ) * X + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * Y)
        * (N : ℝ) ^ (-σ)
      ≤ (N : ℝ) ^ (1 - σ) * (512 * X + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set β : ℝ := 1 - 4 / (2 : ℝ) ^ k with hβdef
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  have hβ0 : (0 : ℝ) ≤ β := by
    have hDpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h1 : 4 / (2 : ℝ) ^ k ≤ 1 := by rw [div_le_one hDpos]; linarith
    rw [hβdef]; linarith
  have hLR : ((M - N : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNsig : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hN0.le _
  have hinner : 256 * (((M - N : ℕ) : ℝ) * X + ((M - N : ℕ) : ℝ) ^ β * Y)
      ≤ (N : ℝ) * (512 * X + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y) := by
    have h1 : 256 * (((M - N : ℕ) : ℝ) * X) ≤ (N : ℝ) * (512 * X) := by
      nlinarith [mul_le_mul_of_nonneg_right hLR hX0, hX0, hN0]
    have hpow : ((M - N : ℕ) : ℝ) ^ β ≤ 2 * (N : ℝ) ^ β := by
      have hstep : ((M - N : ℕ) : ℝ) ^ β ≤ (2 * (N : ℝ)) ^ β := Real.rpow_le_rpow hL0 hLR hβ0
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
      have hgoal : (N : ℝ) * (512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * Y)
          = 512 * (N : ℝ) ^ β * Y := by
        rw [← hmerge]; ring
      rw [hgoal]
      nlinarith [mul_le_mul_of_nonneg_right hpow hY0, hY0]
    linarith
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

/-- **Normalised shifted block bound.** -/
theorem shifted_block_sigma_normalized {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) (ht : 0 < t) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k N M : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hM : M ≤ 2 * N)
    (hlam1 : blockLambda t N k ≤ 1) :
    ‖∑ n ∈ Finset.Ico N M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (N : ℝ) ^ (1 - σ)
        * (512 * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlam0 : 0 < blockLambda t N k := blockLambda_pos ht hN k
  have hX0 : (0 : ℝ) ≤ ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2)) :=
    Real.rpow_nonneg (by positivity) _
  have hY0 : (0 : ℝ) ≤ blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)) := Real.rpow_nonneg hlam0.le _
  have hpre := shifted_phase_prefix_bound t ht hα0 hα1 k N M hk hN hNM hM hlam1
  have hsig := shifted_block_sigma_bound hσ t hα0 N M hN hNM _ hpre
  refine hsig.trans ?_
  have hNα : ((N : ℝ) + α) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
  have hP0 : 0 ≤ 256 * (((M - N : ℕ) : ℝ)
      * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
        + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k))) := by
    have : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) := Real.rpow_nonneg (by positivity) _
    positivity
  calc _ ≤ 256 * (((M - N : ℕ) : ℝ)
        * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
        + ((M - N : ℕ) : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)))
        * (N : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_left hNα hP0
    _ ≤ _ := block_length_absorb (σ := σ) hk hN (by omega) hX0 hY0

/-- **Shifted block saving at the classical scale.** For `σ ≥ 0`, `0 ≤ α ≤ 1`, a block `[N, M)`
with `M ≤ 2N`, `(k₀−1)! ≤ N` and `8πN^{1/3} ≤ t ≤ 2π 2^{k₀} N^{k₀−1} N^{−1/3}`:
`‖Σ_{N≤n<M} (n+α)^{-σ-it}‖ ≤ 2560 N^{1−σ} N^{−1/(3·2^{k₀})}`. -/
theorem shifted_block_sigma_saving_of_small_factorial {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {N M k₀ : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ (k₀ - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, ((((n : ℝ) + α : ℝ)) : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk, hkle, hlowk, hhighk⟩ :=
    exists_blockLambda_in_window ht hN hk₀ (blockLambda_two_ge hN hlow)
      (blockLambda_le_of_small_factorial ht hN (by omega) hfac hhigh)
  have hlam1 : blockLambda t N k ≤ 1 :=
    hhighk.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
  have hlam0 : 0 < blockLambda t N k := blockLambda_pos ht hN k
  have hmono : (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hpk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k₀ := pow_le_pow_right₀ (by norm_num) hkle
    have hpos : (0 : ℝ) < 3 * (2 : ℝ) ^ k := by positivity
    have hle : 1 / (3 * (2 : ℝ) ^ k₀) ≤ 1 / (3 * (2 : ℝ) ^ k) :=
      one_div_le_one_div_of_le hpos (by linarith)
    linarith
  have hNsig : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg hN0.le _
  have hbracket := block_saving_wide k N hk hN _ hlam0 hhighk hlowk
  refine le_trans (shifted_block_sigma_normalized hσ t ht hα0 hα1 k N M hk hN hNM hM hlam1) ?_
  calc (N : ℝ) ^ (1 - σ)
        * (512 * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k)) * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)))
      ≤ (N : ℝ) ^ (1 - σ) * (2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))) :=
        mul_le_mul_of_nonneg_left hbracket hNsig
    _ ≤ (N : ℝ) ^ (1 - σ) * (2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀)))) := by gcongr
    _ = 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by ring

end

end GaloisForLFunctions.MatomakiRadziwill
