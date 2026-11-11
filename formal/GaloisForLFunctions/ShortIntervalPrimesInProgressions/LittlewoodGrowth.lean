import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterPhaseBlocks
import GaloisForLFunctions.RHTower.DirichletLLogStrip
import GaloisForLFunctions.RHTower.VisibleCoprimeDirichletZeroJet

/-!
# Littlewood's growth bound for Dirichlet `L`-functions

For every modulus `q` there is `T₀` such that for every nonprincipal character `χ` modulo `q`,

`|L(σ + it, χ)| ≤ (3 + 4888 q) (log |t|)³`   for `|t| ≥ T₀`, `1 − (log log |t|)²/log |t| ≤ σ ≤ 2`

(`norm_LFunction_le_littlewood`).

Write `L = log t`, `η = (log L)²/L`.  The function is the partial sum over `n < 2^K ≍ t²` up to
`O(q)`.  The dyadic block `[M, 2M)` is bounded trivially by `M^{1−σ} ≤ M^η ≤ L²` while
`M ≤ exp(2L/log L)`.  Above that threshold the `k`-th derivative test is applied at the least
order `k` with `λ_k = (t/2π)(k−1)!/(2M)^k ≤ M^{−1/2}`; minimality gives `λ_k ≥ M^{−3/2}/2`, and
the two terms of the test give `|Σ_{block prefix} χ(n) n^{−it}| ≤ 1536 q M^{1 − 2^{−k−1}}`.  The
order `⌊L/log M⌋ + 3` is admissible, so `2^{k+1} ≤ 16√L`, and Abel summation leaves
`1536 q M^{η − 1/(16√L)} ≤ 1536 q / L²`.
-/

open Complex Finset Filter RHTower.Sieve

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-- The derivative size `λ_k = (t/2π)(k−1)!/(2M)^k` of the `k`-th derivative test on `[M, 2M]`. -/
def blockLam (t : ℝ) (M k : ℕ) : ℝ :=
  t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (M : ℝ)) ^ k

theorem blockLam_pos {t : ℝ} (ht : 0 < t) {M : ℕ} (hM : 1 ≤ M) (k : ℕ) : 0 < blockLam t M k := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold blockLam
  have := Real.pi_pos
  have : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

theorem nat_add_two_le_two_pow {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-! ### The prefix bound at an order with `M^{−3/2}/2 ≤ λ_k ≤ M^{−1/2}` -/

/-- **The saving on a dyadic block.**  At an order `k ≥ 2` with `M^{−3/2}/2 ≤ λ_k ≤ M^{−1/2}`, every
prefix of length at most `M` of `Σ_{n ≥ M} χ(n) n^{−it}` is at most `1536 q M^{1 − 2^{−k−1}}`. -/
theorem norm_character_prefix_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ}
    (ht : 0 < t) {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k)
    (hup : blockLam t M k ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)))
    (hlow : (M : ℝ) ^ (-(3 / 2 : ℝ)) / 2 ≤ blockLam t M k) {ℓ : ℕ} (hℓ : ℓ ≤ M) :
    ‖∑ j ∈ Finset.range ℓ, χ (M + j : ℕ) * ((M + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖
      ≤ q * (1536 * (M : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 1))) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  set lam := blockLam t M k with hlamdef
  have hlam0 : 0 < lam := blockLam_pos ht hM k
  have hlam1 : lam ≤ 1 :=
    hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hM1 (by norm_num))
  refine norm_character_run_le χ t M ℓ _ fun a => ?_
  refine (norm_twisted_block_le t ht a k M ℓ hk hM hℓ0 (by omega) hlam1).trans ?_
  -- the exponent bookkeeping
  set D : ℝ := (2 : ℝ) ^ k with hD
  have hD4 : 4 ≤ D := by
    rw [hD]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hkD : (k : ℝ) ≤ D - 2 := by
    have := nat_add_two_le_two_pow hk
    rw [hD]
    have h : ((k + 2 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    linarith
  have hD2 : (2 : ℝ) ^ (k + 1) = 2 * D := by rw [hD, pow_succ]; ring
  have hℓM : (ℓ : ℝ) ≤ M := by exact_mod_cast hℓ
  have hℓ1 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set e : ℝ := 1 / (D - 2) with he
  have he0 : 0 < e := by rw [he]; apply div_pos one_pos; linarith
  -- first term
  have hX : ((4 : ℝ) ^ k * lam) ^ e ≤ 4 * (M : ℝ) ^ (-(1 / (2 * D))) := by
    have h1 : ((4 : ℝ) ^ k * lam) ^ e ≤ ((4 : ℝ) ^ k * (M : ℝ) ^ (-(1 / 2 : ℝ))) ^ e :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hup (by positivity)) he0.le
    have hsplit : ((4 : ℝ) ^ k * (M : ℝ) ^ (-(1 / 2 : ℝ))) ^ e
        = ((4 : ℝ) ^ k) ^ e * ((M : ℝ) ^ (-(1 / 2 : ℝ))) ^ e :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [hsplit] at h1
    have h2 : ((4 : ℝ) ^ k) ^ e ≤ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      calc (4 : ℝ) ^ ((k : ℝ) * e) ≤ 4 ^ (1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            rw [he, mul_one_div, div_le_one (by linarith)]
            exact hkD
        _ = 4 := Real.rpow_one 4
    have h3 : ((M : ℝ) ^ (-(1 / 2 : ℝ))) ^ e ≤ (M : ℝ) ^ (-(1 / (2 * D))) := by
      rw [← Real.rpow_mul hM0.le]
      refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
      rw [he]
      have hD0 : 0 < D - 2 := by linarith
      rw [neg_mul, neg_le_neg_iff, div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    calc ((4 : ℝ) ^ k * lam) ^ e ≤ ((4 : ℝ) ^ k) ^ e * ((M : ℝ) ^ (-(1 / 2 : ℝ))) ^ e := h1
      _ ≤ 4 * (M : ℝ) ^ (-(1 / (2 * D))) :=
          mul_le_mul h2 h3 (by positivity) (by norm_num)
  -- second term
  have hY : lam ^ (-(2 / D)) ≤ 2 * (M : ℝ) ^ (3 / D) := by
    have h1 : lam ^ (-(2 / D)) ≤ ((M : ℝ) ^ (-(3 / 2 : ℝ)) / 2) ^ (-(2 / D)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by
        have : 0 < 2 / D := by positivity
        linarith)
    have h3 : -(3 / 2 : ℝ) * -(2 / D) = 3 / D := by field_simp
    have hsplit : ((M : ℝ) ^ (-(3 / 2 : ℝ)) / 2) ^ (-(2 / D))
        = (M : ℝ) ^ (3 / D) * (2 : ℝ) ^ (2 / D) := by
      rw [div_eq_mul_inv ((M : ℝ) ^ (-(3 / 2 : ℝ))) 2,
        Real.mul_rpow (by positivity) (by norm_num), ← Real.rpow_mul hM0.le, h3,
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
    rw [hsplit] at h1
    have h2 : (2 : ℝ) ^ (2 / D) ≤ 2 := by
      calc (2 : ℝ) ^ (2 / D) ≤ 2 ^ (1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            rw [div_le_one (by linarith)]
            linarith
        _ = 2 := Real.rpow_one 2
    calc lam ^ (-(2 / D)) ≤ (M : ℝ) ^ (3 / D) * 2 ^ (2 / D) := h1
      _ ≤ (M : ℝ) ^ (3 / D) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * (M : ℝ) ^ (3 / D) := by ring
  have hℓpow : (ℓ : ℝ) ^ (1 - 4 / D) ≤ (M : ℝ) ^ (1 - 4 / D) :=
    Real.rpow_le_rpow hℓ1 hℓM (by rw [sub_nonneg, div_le_one (by linarith)]; exact hD4)
  -- combine
  have hA : (ℓ : ℝ) * ((4 : ℝ) ^ k * lam) ^ e ≤ 4 * (M : ℝ) ^ (1 - 1 / (2 * D)) := by
    calc (ℓ : ℝ) * ((4 : ℝ) ^ k * lam) ^ e ≤ (M : ℝ) * (4 * (M : ℝ) ^ (-(1 / (2 * D)))) :=
          mul_le_mul hℓM hX (by positivity) hM0.le
      _ = 4 * (M : ℝ) ^ (1 - 1 / (2 * D)) := by
          rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]; ring
  have hB : (ℓ : ℝ) ^ (1 - 4 / D) * lam ^ (-(2 / D)) ≤ 2 * (M : ℝ) ^ (1 - 1 / (2 * D)) := by
    calc (ℓ : ℝ) ^ (1 - 4 / D) * lam ^ (-(2 / D))
        ≤ (M : ℝ) ^ (1 - 4 / D) * (2 * (M : ℝ) ^ (3 / D)) :=
          mul_le_mul hℓpow hY (by positivity) (by positivity)
      _ = 2 * (M : ℝ) ^ (1 - 1 / D) := by
          rw [mul_left_comm, ← Real.rpow_add hM0]
          congr 2
          ring
      _ ≤ 2 * (M : ℝ) ^ (1 - 1 / (2 * D)) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM1 ?_) (by norm_num)
          have : 1 / (2 * D) ≤ 1 / D :=
            one_div_le_one_div_of_le (by linarith) (by linarith)
          linarith
  rw [hD2]
  calc 256 * ((ℓ : ℝ) * ((4 : ℝ) ^ k * lam) ^ (1 / ((2 : ℝ) ^ k - 2))
        + (ℓ : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(2 / (2 : ℝ) ^ k)))
      ≤ 256 * (4 * (M : ℝ) ^ (1 - 1 / (2 * D)) + 2 * (M : ℝ) ^ (1 - 1 / (2 * D))) := by
        rw [← hD, ← he]
        linarith
    _ = 1536 * (M : ℝ) ^ (1 - 1 / (2 * D)) := by ring

/-! ### Abel summation and the trivial bound -/

theorem natCast_cpow_split (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(I * (t : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show -((σ : ℂ) + (t : ℂ) * I) = ((-σ : ℝ) : ℂ) + -(I * (t : ℂ)) by push_cast; ring,
    Complex.cpow_add _ _ hn0, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

/-- **Abel summation on a block.**  Prefix bounds `P` for `Σ χ(n) n^{−it}` give
`|Σ_{M ≤ n < M'} χ(n) n^{−σ−it}| ≤ P M^{−σ}`. -/
theorem norm_character_block_sigma_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ t : ℝ} (hσ : 0 ≤ σ) {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') (P : ℝ)
    (hP : ∀ m, M ≤ m → m ≤ M' →
      ‖∑ n ∈ Finset.Ico M m, χ n * (n : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico M M', χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ P * (M : ℝ) ^ (-σ) := by
  have hterm : ∀ n ∈ Finset.Ico M M', χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (χ n * (n : ℂ) ^ (-(I * (t : ℂ)))) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [natCast_cpow_split n (by omega) σ t]
    ring
  rw [Finset.sum_congr rfl hterm]
  refine abel_block_bound (fun n => χ n * (n : ℂ) ^ (-(I * (t : ℂ))))
    (fun n => (n : ℝ) ^ (-σ)) M M' hMM' (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ P hP
  intro m hm _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith) (by linarith)

/-- **The trivial block bound.**  `|Σ_{M ≤ n < 2M} χ(n) n^{−s}| ≤ M^{1−σ}`. -/
theorem norm_character_block_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ t : ℝ} (hσ : 0 ≤ σ) {M : ℕ} (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Ico M (2 * M), χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ (M : ℝ) ^ (1 - σ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hterm : ∀ n ∈ Finset.Ico M (2 * M),
      ‖χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ (M : ℝ) ^ (-σ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have hre : (-((σ : ℂ) + (t : ℂ) * I)).re = -σ := by simp
    rw [hre]
    calc ‖χ n‖ * (n : ℝ) ^ (-σ) ≤ 1 * (M : ℝ) ^ (-σ) :=
          mul_le_mul (DirichletCharacter.norm_le_one χ n)
            (Real.rpow_le_rpow_of_nonpos hM0 (by exact_mod_cast hn.1) (by linarith))
            (by positivity) zero_le_one
      _ = (M : ℝ) ^ (-σ) := one_mul _
  calc ‖∑ n ∈ Finset.Ico M (2 * M), χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ ∑ _n ∈ Finset.Ico M (2 * M), (M : ℝ) ^ (-σ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (M : ℝ) * (M : ℝ) ^ (-σ) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        congr 1
        push_cast [show 2 * M - M = M by omega]
        ring
    _ = (M : ℝ) ^ (1 - σ) := by
        rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]

/-! ### The order -/

theorem blockLam_succ {t : ℝ} {M : ℕ} (hM : 1 ≤ M) {j : ℕ} (hj : 1 ≤ j) :
    blockLam t M (j + 1) = blockLam t M j * ((j : ℝ) / (2 * M)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold blockLam
  simp only [Nat.add_sub_cancel]
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- **The least admissible order.**  If some order `k₁ ≥ 2` has `λ_{k₁} ≤ M^{−1/2}` and
`t ≥ 4π√M`, the least such order `k` also has `λ_k ≥ M^{−3/2}/2`. -/
theorem exists_good_order {t : ℝ} (ht : 0 < t) {M k₁ : ℕ} (hM : 1 ≤ M) (hk₁ : 2 ≤ k₁)
    (hk₁lam : blockLam t M k₁ ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)))
    (htM : 4 * Real.pi * Real.sqrt M ≤ t) :
    ∃ k, 2 ≤ k ∧ k ≤ k₁ ∧ blockLam t M k ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)) ∧
      (M : ℝ) ^ (-(3 / 2 : ℝ)) / 2 ≤ blockLam t M k := by
  classical
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hex : ∃ k, 2 ≤ k ∧ blockLam t M k ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)) := ⟨k₁, hk₁, hk₁lam⟩
  obtain ⟨hk2, hklam⟩ := Nat.find_spec hex
  have hmin : Nat.find hex ≤ k₁ := Nat.find_min' hex ⟨hk₁, hk₁lam⟩
  refine ⟨Nat.find hex, hk2, hmin, hklam, ?_⟩
  set k := Nat.find hex with hkdef
  have h32 : (M : ℝ) ^ (-(3 / 2 : ℝ)) = (M : ℝ) ^ (-(1 / 2 : ℝ)) / M := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hM0, Real.rpow_neg_one]
    ring
  rcases Nat.eq_or_lt_of_le hk2 with h2 | hlt
  · -- the order two: `λ_2 = t/(8πM²)`
    rw [← h2]
    have hπ := Real.pi_pos
    have hsq : Real.sqrt M = (M : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0.le
    have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
    have hM32 : (M : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / (Real.sqrt M * M) := by
      rw [h32, Real.rpow_neg hM0.le, ← hsq]
      field_simp
    have hlam2 : blockLam t M 2 = t / (8 * Real.pi * (M : ℝ) ^ 2) := by
      unfold blockLam
      simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.factorial_one, Nat.cast_one, mul_one]
      field_simp
      ring
    rw [hM32, hlam2, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 4 * Real.pi * Real.sqrt M * (Real.sqrt M * M * 2) ≤ t * (Real.sqrt M * M * 2) :=
      mul_le_mul_of_nonneg_right htM (by positivity)
    have heq : 4 * Real.pi * Real.sqrt M * (Real.sqrt M * M * 2) = 1 * (8 * Real.pi * (M : ℝ) ^ 2) := by
      linear_combination (8 * Real.pi * M) * hsM
    linarith
  · -- above the order two the previous order fails
    have hprev : ¬ (2 ≤ k - 1 ∧ blockLam t M (k - 1) ≤ (M : ℝ) ^ (-(1 / 2 : ℝ))) :=
      Nat.find_min hex (show k - 1 < k by omega)
    have hgt : (M : ℝ) ^ (-(1 / 2 : ℝ)) < blockLam t M (k - 1) := by
      by_contra hcon
      exact hprev ⟨by omega, not_lt.mp hcon⟩
    have hrec := blockLam_succ (t := t) hM (j := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hrec
    rw [hrec, h32]
    have hj : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
    have hfrac : 1 / (2 * (M : ℝ)) ≤ ((k - 1 : ℕ) : ℝ) / (2 * M) :=
      div_le_div_of_nonneg_right hj (by positivity)
    have hpos : 0 < (M : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hM0 _
    calc (M : ℝ) ^ (-(1 / 2 : ℝ)) / M / 2 = (M : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / (2 * M)) := by
          field_simp
      _ ≤ blockLam t M (k - 1) * (((k - 1 : ℕ) : ℝ) / (2 * M)) :=
          mul_le_mul hgt.le hfrac (by positivity) (blockLam_pos ht hM _).le

/-- **An admissible order.**  With `f = ⌊log t / log M⌋`, the order `f + 3` has
`λ_{f+3} ≤ M^{−1/2}` as soon as `(f + 2)! ≤ M`. -/
theorem blockLam_floor_le {t : ℝ} (ht : 1 < t) {M : ℕ} (hM : 2 ≤ M)
    (hfac : ((Nat.factorial (⌊Real.log t / Real.log M⌋₊ + 2)) : ℝ) ≤ M) :
    blockLam t M (⌊Real.log t / Real.log M⌋₊ + 3) ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set f := ⌊Real.log t / Real.log M⌋₊ with hf
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have ht0 : 0 < t := by linarith
  have hπ := Real.pi_pos
  -- `M^{f+1} ≥ t`
  have hpow : t ≤ (M : ℝ) ^ (f + 1) := by
    have hle : Real.log t / Real.log M ≤ ((f + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc t = Real.exp (Real.log M * (Real.log t / Real.log M)) := by
          rw [mul_div_cancel₀ _ hlogM.ne', Real.exp_log ht0]
      _ ≤ Real.exp (Real.log M * ((f + 1 : ℕ) : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hlogM.le)
      _ = (M : ℝ) ^ (f + 1) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hM0]
  have hfac0 : (0 : ℝ) < (Nat.factorial (f + 2) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold blockLam
  simp only [show f + 3 - 1 = f + 2 by omega]
  have h2pow : (M : ℝ) ^ (f + 3) ≤ (2 * (M : ℝ)) ^ (f + 3) :=
    pow_le_pow_left₀ hM0.le (by linarith) _
  have hden : t * (M : ℝ) ^ 2 ≤ (2 * (M : ℝ)) ^ (f + 3) := by
    calc t * (M : ℝ) ^ 2 ≤ (M : ℝ) ^ (f + 1) * (M : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (M : ℝ) ^ (f + 3) := by rw [← pow_add]
      _ ≤ _ := h2pow
  have hMinv : (M : ℝ)⁻¹ ≤ (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hM1.le (by norm_num)
  refine le_trans ?_ hMinv
  rw [div_le_iff₀ (by positivity)]
  have h2π : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc t / (2 * Real.pi) * (Nat.factorial (f + 2) : ℝ)
      ≤ t * (Nat.factorial (f + 2) : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hfac0.le
        exact div_le_self ht0.le h2π
    _ ≤ t * M := mul_le_mul_of_nonneg_left hfac ht0.le
    _ = (M : ℝ)⁻¹ * (t * (M : ℝ) ^ 2) := by field_simp
    _ ≤ (M : ℝ)⁻¹ * (2 * (M : ℝ)) ^ (f + 3) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-! ### The blocks at a large height -/

/-- The width `η(t) = (log log t)²/log t` of Littlewood's growth region. -/
def litEta (t : ℝ) : ℝ := Real.log (Real.log t) ^ 2 / Real.log t

/-- `(x : ℝ)^n = exp(n log x)` for `x > 0`. -/
theorem pow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp (n * Real.log x) := by
  rw [← Real.log_pow, Real.exp_log (pow_pos hx n)]

/-- **A saving block.**  Above `exp(2L/log L)`, a dyadic block of `L(s, χ)` is at most
`1536 q/L²` on Littlewood's region, `L = log t`. -/
theorem norm_character_block_saving {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ t : ℝ} (ht : 1 < t) (hL4 : 4 ≤ Real.log (Real.log t))
    (hc1 : 32 * Real.log (Real.log t) ^ 2 ≤ Real.sqrt (Real.log t))
    (hc2 : Real.log (Real.log t) ^ 2 * Real.log (Real.log (Real.log t)) ≤ 2 * Real.log t)
    (hσ0 : 0 ≤ σ) (hσ : 1 - litEta t ≤ σ) {M : ℕ}
    (hMlow : Real.exp (2 * Real.log t / Real.log (Real.log t)) < M)
    (hMt : 4 * Real.pi * Real.sqrt M ≤ t) :
    ‖∑ n ∈ Finset.Ico M (2 * M), χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ q * 1536 / Real.log t ^ 2 := by
  set L := Real.log t with hLdef
  set ℓL := Real.log L with hℓL
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := Real.log_pos ht
  have hℓL0 : 0 < ℓL := by linarith
  have hexp0 := Real.exp_pos (2 * L / ℓL)
  have hM1R : (1 : ℝ) < M := lt_of_le_of_lt (Real.one_le_exp (by positivity)) hMlow
  have hM2 : 2 ≤ M := by
    have : 1 < M := by exact_mod_cast hM1R
    omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 2 * L / ℓL < Real.log M := by
    rw [← Real.log_exp (2 * L / ℓL)]
    exact Real.log_lt_log hexp0 hMlow
  have hlogM0 : 0 < Real.log M := lt_of_le_of_lt (by positivity) hlogM
  -- the admissible order `f + 3`
  set f := ⌊L / Real.log M⌋₊ with hf
  have hfL : (f : ℝ) ≤ ℓL / 2 := by
    have h1 : (f : ℝ) ≤ L / Real.log M := Nat.floor_le (by positivity)
    have h2 : L / Real.log M ≤ ℓL / 2 := by
      rw [div_le_div_iff₀ hlogM0 (by norm_num)]
      have := (div_lt_iff₀ hℓL0).mp hlogM
      nlinarith
    linarith
  have hfac : ((Nat.factorial (f + 2)) : ℝ) ≤ M := by
    have h1 : ((Nat.factorial (f + 2)) : ℝ) ≤ ((f + 2 : ℕ) : ℝ) ^ (f + 2) := by
      exact_mod_cast Nat.factorial_le_pow (f + 2)
    have hf2 : ((f + 2 : ℕ) : ℝ) ≤ ℓL := by push_cast; linarith
    have hf2pos : (0 : ℝ) < ((f + 2 : ℕ) : ℝ) := by positivity
    have h2 : ((f + 2 : ℕ) : ℝ) ^ (f + 2) ≤ Real.exp (ℓL * Real.log ℓL) := by
      rw [pow_eq_exp_mul_log hf2pos]
      refine Real.exp_le_exp.mpr (mul_le_mul hf2 (Real.log_le_log hf2pos hf2) ?_ hℓL0.le)
      exact Real.log_nonneg (by push_cast; linarith)
    have h3 : ℓL * Real.log ℓL ≤ 2 * L / ℓL := by
      rw [le_div_iff₀ hℓL0]
      nlinarith
    calc ((Nat.factorial (f + 2)) : ℝ) ≤ Real.exp (ℓL * Real.log ℓL) := h1.trans h2
      _ ≤ Real.exp (2 * L / ℓL) := Real.exp_le_exp.mpr h3
      _ ≤ M := hMlow.le
  have hk₁ := blockLam_floor_le ht hM2 hfac
  obtain ⟨k, hk2, hkk₁, hup, hlow⟩ :=
    exists_good_order ht0 (by omega) (by omega) hk₁ hMt
  -- the prefix bounds and Abel summation
  have hP : ∀ m, M ≤ m → m ≤ 2 * M →
      ‖∑ n ∈ Finset.Ico M m, χ n * (n : ℂ) ^ (-(I * (t : ℂ)))‖
        ≤ q * (1536 * (M : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 1))) := by
    intro m hm1 hm2
    rw [Finset.sum_Ico_eq_sum_range]
    exact norm_character_prefix_le χ ht0 (by omega) hk2 hup hlow (by omega)
  have hblock := norm_character_block_sigma_le χ hσ0 (by omega) (by omega) _ hP
  refine hblock.trans ?_
  -- the exponent
  have h2k : (2 : ℝ) ^ (k + 1) ≤ 16 * Real.sqrt L := by
    have hkk₁' : k ≤ f + 3 := hkk₁
    have h1 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (f + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ f ≤ Real.sqrt L := by
      calc (2 : ℝ) ^ f ≤ Real.exp 1 ^ f :=
            pow_le_pow_left₀ (by norm_num) (Real.exp_one_gt_d9.le.trans' (by norm_num)) f
        _ = Real.exp f := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ Real.exp (ℓL / 2) := Real.exp_le_exp.mpr hfL
        _ = Real.sqrt L := by
            rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hL0, hℓL]
            ring_nf
    calc (2 : ℝ) ^ (k + 1) ≤ 2 ^ (f + 4) := h1
      _ = 16 * 2 ^ f := by ring
      _ ≤ 16 * Real.sqrt L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hη : litEta t ≤ 1 / (32 * Real.sqrt L) := by
    unfold litEta
    rw [← hLdef, ← hℓL, div_le_div_iff₀ hL0 (by positivity)]
    have : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    nlinarith
  have hexpo : 1 - 1 / (2 : ℝ) ^ (k + 1) + -σ ≤ -(1 / (32 * Real.sqrt L)) := by
    have h1 : 1 / (16 * Real.sqrt L) ≤ 1 / (2 : ℝ) ^ (k + 1) :=
      one_div_le_one_div_of_le (by positivity) h2k
    have h2 : 1 / (16 * Real.sqrt L) = 2 * (1 / (32 * Real.sqrt L)) := by field_simp; ring
    linarith
  have hMpow : (M : ℝ) ^ (-(1 / (32 * Real.sqrt L))) ≤ 1 / L ^ 2 := by
    rw [Real.rpow_def_of_pos hM0]
    have hgoal : Real.log M * -(1 / (32 * Real.sqrt L)) ≤ -(2 * ℓL) := by
      have h1 : 2 * L / ℓL / (32 * Real.sqrt L) ≤ Real.log M / (32 * Real.sqrt L) :=
        div_le_div_of_nonneg_right hlogM.le (by positivity)
      have h2 : 2 * ℓL ≤ 2 * L / ℓL / (32 * Real.sqrt L) := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
        nlinarith
      have h3 : Real.log M * -(1 / (32 * Real.sqrt L)) = -(Real.log M / (32 * Real.sqrt L)) := by
        ring
      linarith
    calc Real.exp (Real.log M * -(1 / (32 * Real.sqrt L))) ≤ Real.exp (-(2 * ℓL)) :=
          Real.exp_le_exp.mpr hgoal
      _ = 1 / L ^ 2 := by
          rw [Real.exp_neg, show 2 * ℓL = 2 * Real.log L from rfl, ← Real.log_rpow hL0,
            Real.exp_log (by positivity), one_div]
          norm_cast
  calc q * (1536 * (M : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 1))) * (M : ℝ) ^ (-σ)
      = q * 1536 * (M : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k + 1) + -σ) := by
        rw [Real.rpow_add hM0]; ring
    _ ≤ q * 1536 * (M : ℝ) ^ (-(1 / (32 * Real.sqrt L))) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM1R.le hexpo)
          (by positivity)
    _ ≤ q * 1536 * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hMpow (by positivity)
    _ = q * 1536 / L ^ 2 := by ring

/-- **A trivial block.**  Below `exp(2L/log L)` a dyadic block is at most `L²` on Littlewood's
region. -/
theorem norm_character_block_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ t : ℝ} (ht : 1 < t) (hℓ : 0 < Real.log (Real.log t)) (hσ0 : 0 ≤ σ)
    (hσ : 1 - litEta t ≤ σ) {M : ℕ} (hM : 1 ≤ M)
    (hMhigh : (M : ℝ) ≤ Real.exp (2 * Real.log t / Real.log (Real.log t))) :
    ‖∑ n ∈ Finset.Ico M (2 * M), χ n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ Real.log t ^ 2 := by
  have hL0 : 0 < Real.log t := Real.log_pos ht
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hη0 : 0 ≤ litEta t := by unfold litEta; positivity
  refine (norm_character_block_trivial χ hσ0 hM).trans ?_
  calc (M : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (litEta t) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    _ ≤ (Real.exp (2 * Real.log t / Real.log (Real.log t))) ^ (litEta t) :=
        Real.rpow_le_rpow (by linarith) hMhigh hη0
    _ = Real.log t ^ 2 := by
        rw [← Real.exp_mul]
        unfold litEta
        have : 2 * Real.log t / Real.log (Real.log t) *
            (Real.log (Real.log t) ^ 2 / Real.log t) = 2 * Real.log (Real.log t) := by
          field_simp
        rw [this, show 2 * Real.log (Real.log t) = ((2 : ℕ) : ℝ) * Real.log (Real.log t) by
          norm_num, Real.exp_nat_mul, Real.exp_log hL0]

/-- The dyadic decomposition `Σ_{1 ≤ n < 2^K} = Σ_{m < K} Σ_{2^m ≤ n < 2^{m+1}}`. -/
theorem sum_Ico_one_two_pow (f : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ K), f n = ∑ m ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ m) (2 * 2 ^ m), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * 2 ^ K = 2 ^ (K + 1) by ring,
      Finset.sum_Ico_consecutive _ (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ K))]

/-! ### Littlewood's bound -/

/-- The three growth conditions on `L = log t`, eventually. -/
theorem eventually_littlewood_conditions :
    ∀ᶠ L : ℝ in atTop, 4 ≤ Real.log L ∧ 32 * Real.log L ^ 2 ≤ Real.sqrt L ∧
      Real.log L ^ 2 * Real.log (Real.log L) ≤ 2 * L := by
  have h4 := Real.tendsto_log_atTop.eventually_ge_atTop 4
  have ho4 := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (c := 1 / 1024) (by norm_num)
  have ho3 := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound (c := 1) one_pos
  filter_upwards [h4, ho4, ho3, eventually_ge_atTop 1] with L h4 ho4 ho3 hL1
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), id,
    abs_of_nonneg (by linarith)] at ho4 ho3
  refine ⟨h4, ?_, ?_⟩
  · rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith
  · have hll : Real.log (Real.log L) ≤ Real.log L := Real.log_le_self hlog0
    calc Real.log L ^ 2 * Real.log (Real.log L) ≤ Real.log L ^ 2 * Real.log L :=
          mul_le_mul_of_nonneg_left hll (by positivity)
      _ = Real.log L ^ 3 := by ring
      _ ≤ 1 * L := ho3
      _ ≤ 2 * L := by linarith

/-- **Littlewood's growth bound at positive heights.** -/
theorem norm_LFunction_le_littlewood_pos (q : ℕ) [NeZero q] :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ t : ℝ, T₀ ≤ t →
      1 - litEta t ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (3 + 4888 * q) * Real.log t ^ 3 := by
  have hev : ∀ᶠ t : ℝ in atTop, (4 ≤ Real.log (Real.log t) ∧
      32 * Real.log (Real.log t) ^ 2 ≤ Real.sqrt (Real.log t) ∧
      Real.log (Real.log t) ^ 2 * Real.log (Real.log (Real.log t)) ≤ 2 * Real.log t) ∧
      400 ≤ t :=
    (Real.tendsto_log_atTop.eventually eventually_littlewood_conditions).and
      (eventually_ge_atTop 400)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨max T₁ 400, by linarith [le_max_right T₁ 400], ?_⟩
  intro χ hχ σ t ht hσ hσ2
  obtain ⟨⟨h4, hc1, hc2⟩, h400⟩ := hT₁ t (le_of_max_le_left ht)
  set L := Real.log t with hLdef
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := Real.log_pos ht1
  have hℓ0 : 0 < Real.log L := by linarith
  have hL1 : 1 < L := by
    by_contra h
    have : Real.log L ≤ 0 := Real.log_nonpos hL0.le (not_lt.mp h)
    linarith
  have hsL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left hL0.le]; nlinarith
  have hη : litEta t ≤ 1 / 2 := by
    unfold litEta
    rw [← hLdef, div_le_iff₀ hL0]
    nlinarith
  have hσ12 : 1 / 2 ≤ σ := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  -- the number of dyadic blocks
  set K := Nat.log 2 ⌊t ^ 2 / 200⌋₊ with hK
  have hfl : 1 ≤ ⌊t ^ 2 / 200⌋₊ := by
    rw [Nat.one_le_floor_iff]
    nlinarith
  have hK1 : (2 : ℝ) ^ K ≤ t ^ 2 / 200 := by
    have h1 : 2 ^ K ≤ ⌊t ^ 2 / 200⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ K : ℕ) : ℝ) ≤ (⌊t ^ 2 / 200⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by positivity))
  have hK2 : t ^ 2 / 400 < (2 : ℝ) ^ K := by
    have h1 : ⌊t ^ 2 / 200⌋₊ < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : (⌊t ^ 2 / 200⌋₊ : ℝ) + 1 ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one (t ^ 2 / 200)
    push_cast at h2
    rw [pow_succ] at h2
    linarith
  have hK3 : (K : ℝ) ≤ 3 * L := by
    have h1 : (2 : ℝ) ^ K ≤ t ^ 2 := by nlinarith
    have h2 : (K : ℝ) * Real.log 2 ≤ 2 * L := by
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have h3 := Real.log_two_gt_d9
    nlinarith
  -- the truncation
  have hpart : RHTower.dirichletPartialSum (fun j => χ (j + 1)) (2 ^ K - 1) s
      = ∑ n ∈ Finset.Ico 1 (2 ^ K), χ n * (n : ℂ) ^ (-s) := by
    unfold RHTower.dirichletPartialSum
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  have herr := RHTower.norm_LFunction_sub_character_partial_le hχ (s := s) (by rw [hsre]; linarith)
    (2 ^ K - 1)
  rw [hpart, hsre] at herr
  have hcast : (((2 ^ K - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ K := by
    have : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at herr
  have hsnorm : ‖s‖ ≤ 2 + t := by
    calc ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ ≤ 2 + t := by rw [abs_of_nonneg hσ0, abs_of_pos ht0]; linarith
  have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hdecay : (2 : ℝ) ^ K ^ (-σ) ≤ 20 / t := by
    have h1 : ((2 : ℝ) ^ K) ^ (-σ) ≤ ((2 : ℝ) ^ K) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le h2K1 (by linarith)
    have h2 : ((2 : ℝ) ^ K) ^ (-(1 / 2 : ℝ)) ≤ (t ^ 2 / 400) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hK2.le (by norm_num)
    have h3 : (t ^ 2 / 400) ^ (-(1 / 2 : ℝ)) = 20 / t := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
        show t ^ 2 / 400 = (t / 20) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      field_simp
    exact h1.trans (h2.trans h3.le)
  have herr' : ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Ico 1 (2 ^ K), χ n * (n : ℂ) ^ (-s)‖
      ≤ 120 * q := by
    refine herr.trans ?_
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h1 : 1 + ‖s‖ / σ ≤ 5 + 2 * t := by
      rw [div_le_iff₀ (by linarith)] at *
      have : ‖s‖ / σ ≤ 2 * (2 + t) := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    calc 2 * (q : ℝ) * (1 + ‖s‖ / σ) * ((2 : ℝ) ^ K) ^ (-σ)
        ≤ 2 * q * (5 + 2 * t) * (20 / t) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hdecay
            (by positivity) (by positivity)
      _ = 40 * q * (5 / t + 2) := by field_simp; ring
      _ ≤ 40 * q * 3 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : 5 / t ≤ 1 := by rw [div_le_one ht0]; linarith
          linarith
      _ = 120 * q := by ring
  -- the blocks
  have hblock : ∀ m ∈ Finset.range K,
      ‖∑ n ∈ Finset.Ico (2 ^ m) (2 * 2 ^ m), χ n * (n : ℂ) ^ (-s)‖ ≤ L ^ 2 + q * 1536 / L ^ 2 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hq0 : (0 : ℝ) ≤ q * 1536 / L ^ 2 := by positivity
    have hM : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    by_cases hsmall : ((2 ^ m : ℕ) : ℝ) ≤ Real.exp (2 * Real.log t / Real.log (Real.log t))
    · have := norm_character_block_small χ ht1 hℓ0 hσ0 hσ hM hsmall
      linarith
    · have hMt : 4 * Real.pi * Real.sqrt ((2 ^ m : ℕ) : ℝ) ≤ t := by
        have h1 : ((2 ^ m : ℕ) : ℝ) * 2 ≤ (2 : ℝ) ^ K := by
          have : 2 ^ m * 2 ≤ 2 ^ K := by
            rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) hm
          exact_mod_cast this
        have h2 : Real.sqrt ((2 ^ m : ℕ) : ℝ) ≤ t / 20 := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
        have hπ := Real.pi_lt_d2
        nlinarith [Real.pi_pos]
      have := norm_character_block_saving χ ht1 h4 hc1 hc2 hσ0 hσ (not_le.mp hsmall) hMt
      linarith
  have hsum : ‖∑ n ∈ Finset.Ico 1 (2 ^ K), χ n * (n : ℂ) ^ (-s)‖ ≤ 3 * L ^ 3 + 4608 * q := by
    rw [sum_Ico_one_two_pow]
    calc ‖∑ m ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ m) (2 * 2 ^ m), χ n * (n : ℂ) ^ (-s)‖
        ≤ ∑ _m ∈ Finset.range K, (L ^ 2 + q * 1536 / L ^ 2) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
      _ = K * (L ^ 2 + q * 1536 / L ^ 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 3 * L * (L ^ 2 + q * 1536 / L ^ 2) :=
          mul_le_mul_of_nonneg_right hK3 (by positivity)
      _ = 3 * L ^ 3 + 4608 * q * (1 / L) := by field_simp; ring
      _ ≤ 3 * L ^ 3 + 4608 * q * 1 := by
          have : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
          have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          nlinarith
      _ = 3 * L ^ 3 + 4608 * q := by ring
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1.le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Ico 1 (2 ^ K), χ n * (n : ℂ) ^ (-s)‖
        + ‖∑ n ∈ Finset.Ico 1 (2 ^ K), χ n * (n : ℂ) ^ (-s)‖ := norm_le_norm_sub_add _ _
    _ ≤ 120 * q + (3 * L ^ 3 + 4608 * q) := add_le_add herr' hsum
    _ ≤ (3 + 4888 * q) * L ^ 3 := by nlinarith

/-- **Littlewood's growth bound.**  For every modulus `q` there is `T₀` such that every
nonprincipal `χ` modulo `q` has `|L(σ + it, χ)| ≤ (3 + 4888 q)(log |t|)³` for `|t| ≥ T₀` and
`1 − (log log |t|)²/log |t| ≤ σ ≤ 2`. -/
theorem norm_LFunction_le_littlewood (q : ℕ) [NeZero q] :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ t : ℝ, T₀ ≤ |t| →
      1 - litEta |t| ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (3 + 4888 * q) * Real.log |t| ^ 3 := by
  obtain ⟨T₀, hT₀, hpos⟩ := norm_LFunction_le_littlewood_pos q
  refine ⟨T₀, hT₀, fun χ hχ σ t ht hσ hσ2 => ?_⟩
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht hσ ⊢
    exact hpos χ hχ σ t ht hσ hσ2
  · rw [abs_of_neg h0] at ht hσ ⊢
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
    have h := RHTower.LFunction_inv_conj χ⁻¹ hinv ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)
    rw [inv_inv] at h
    have hconj : (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) = (σ : ℂ) + (t : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hconj] at h
    rw [h, RCLike.norm_conj]
    exact hpos χ⁻¹ hinv σ (-t) ht hσ hσ2

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
