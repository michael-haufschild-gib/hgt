import GaloisForLFunctions.RHTower.ZetaFiveSeventhsLineBound
import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsWeylBlock

/-!
# `ζ` on the line `Re s = 11/18`: the exponent `1/9`

For `t ≥ 1024π`, `‖ζ(11/18 + it)‖ ≤ 10⁷ t^{1/9} log t` (`norm_riemannZeta_elevenEighteenths_le`).
This is the exponent pair `(1/9, 13/18) = A·B·A²·B(0, 1)`: Weyl differencing, the `B`-process, the
fourth-derivative test, on the critical range of blocks.

**Proof.**  Truncate at `K ≥ t²` (`norm_riemannZeta_le_partialSum`), take absolute values below
`c = ⌈t^{2/7}⌉ + 3` (head `≤ 8t^{1/9}`), and bound each dyadic block `[N, 2N)` of `n^{−11/18−it}`
by `10⁶ t^{1/9}` (`norm_eeBlock_le`):
* `3t ≤ 4πN`: Kuzmin–Landau;
* `t⁷ ≤ N¹¹`, `N < t`: second-derivative test;
* `t ≤ N²`, `N¹¹ < t⁷`: third-derivative test;
* `t⁵ ≤ N¹³`, `N² < t`: the `B` range (`norm_prefix_le_BRange`);
* `N¹³ < t⁵`: fourth-derivative test.
Each regime closes by comparing logarithms of monomials `N^a t^b`.  There are at most `4 log t`
blocks.
-/

namespace RHTower

open RHTower.Sieve Finset Complex

noncomputable section

/-! ## From prefix to block -/

/-- A prefix bound on `Σ_{j<L} (N + j)^{−it}`, `1 ≤ L ≤ N`, bounds the weighted dyadic block. -/
theorem block_of_prefix {σ t : ℝ} (hσ : 0 ≤ σ) {N : ℕ} (hN : 1 ≤ N) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ L : ℕ, 1 ≤ L → L ≤ N →
      ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ P * (N : ℝ) ^ (-σ) := by
  refine dirichlet_block_sigma_bound hσ t N (2 * N) hN (by omega) P ?_
  intro m hm1 hm2
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]; exact hP0
  · rw [Finset.sum_Ico_eq_sum_range]
    exact hP (m - N) (by omega) (by omega)

/-! ## Logarithmic constants -/

theorem log_two_bounds : 0.69 < Real.log 2 ∧ Real.log 2 < 0.7 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> linarith

/-! ## The five regimes at `σ = 11/18` -/

/-- **Fourth-derivative block.**  For `3t ≤ 16πN⁴` and `N¹³ ≤ t⁵`: `≤ 672 t^{1/9}`. -/
theorem norm_eeBlock_le_fourth {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (hlam : 3 * t ≤ 16 * Real.pi * (N : ℝ) ^ 4) (h13 : (N : ℝ) ^ 13 ≤ t ^ 5) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 672 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  set lam := 3 * t / (16 * Real.pi * (N : ℝ) ^ 4) with hlamd
  have hlam1 : lam ≤ 1 := by rw [hlamd, div_le_one (by positivity)]; exact hlam
  have hlam0 : 0 < lam := by positivity
  set P := 224 * ((N : ℝ) * lam ^ (1 / 14 : ℝ) + (N : ℝ) ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
    with hP
  have hblk := block_of_prefix (σ := 11 / 18) (t := t) (by norm_num) hN (P := P) (by positivity)
    (fun L hL1 hLN => by
      refine (dirichlet_block_bound_fourth_sharp ht0 hN hL1 (by omega) hlam1).trans ?_
      have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
      have hs : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hLN' (by norm_num)
      rw [hP]
      gcongr)
  refine hblk.trans ?_
  have hlN : 13 * Real.log (N : ℝ) ≤ 5 * Real.log t := by
    have := Real.log_le_log (by positivity) h13
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hlN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  -- `λ ≤ t/N⁴` and `λ ≥ t/(17N⁴)`
  have hs : 0 < t * (N : ℝ) ^ 4 := by positivity
  have hlup : lam ≤ t / (N : ℝ) ^ 4 := by
    rw [hlamd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hpi) hs]
  have hllo : t / (17 * (N : ℝ) ^ 4) ≤ lam := by
    rw [hlamd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hpi4) hs]
  have hA : (N : ℝ) * lam ^ (1 / 14 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)) ≤ t ^ (1 / 9 : ℝ) := by
    have h1 : lam ^ (1 / 14 : ℝ) ≤ (t / (N : ℝ) ^ 4) ^ (1 / 14 : ℝ) :=
      Real.rpow_le_rpow hlam0.le hlup (by norm_num)
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hN0.le)
      (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow hN0, Real.log_rpow ht0,
      Real.log_div ht0.ne' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hB : (N : ℝ) ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) * (N : ℝ) ^ (-(11 / 18 : ℝ))
      ≤ 2 * t ^ (1 / 9 : ℝ) := by
    have h1 : lam ^ (-(1 / 14 : ℝ)) ≤ (t / (17 * (N : ℝ) ^ 4)) ^ (-(1 / 14 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hllo (by norm_num)
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
      (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    have h17 : Real.log 17 ≤ 5 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_rpow hN0, Real.log_rpow (by positivity),
      Real.log_rpow hN0, Real.log_rpow ht0, Real.log_div ht0.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    nlinarith
  have e : P * (N : ℝ) ^ (-(11 / 18 : ℝ))
      = 224 * ((N : ℝ) * lam ^ (1 / 14 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))
        + (N : ℝ) ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) * (N : ℝ) ^ (-(11 / 18 : ℝ))) := by
    rw [hP]; ring
  rw [e]
  linarith

/-- **The `B`-range block.**  For `1024π ≤ t`, `t⁵ ≤ N¹³`, `N² ≤ t`: `≤ 10⁶ t^{1/9}`. -/
theorem norm_eeBlock_le_B {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (h5 : t ^ 5 ≤ (N : ℝ) ^ 13) (h2 : (N : ℝ) ^ 2 ≤ t) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 10 ^ 6 * t ^ (1 / 9 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith [Real.pi_pos]
  have hblk := block_of_prefix (σ := 11 / 18) (t := t) (by norm_num) hN
    (P := 10 ^ 6 * (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) (by positivity)
    (fun L _ hLN => norm_prefix_le_BRange ht h5 h2 hLN)
  refine hblk.trans (le_of_eq ?_)
  have h1 : (N : ℝ) ^ (11 / 18 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)) = 1 := by
    rw [← Real.rpow_add hN0]; norm_num
  calc 10 ^ 6 * (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))
      = 10 ^ 6 * t ^ (1 / 9 : ℝ) * ((N : ℝ) ^ (11 / 18 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))) := by
        ring
    _ = _ := by rw [h1, mul_one]

/-- **Third-derivative block.**  For `t ≤ N²` and `N¹¹ ≤ t⁷`: `≤ 384 t^{1/9}`. -/
theorem norm_eeBlock_le_third {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (h2 : t ≤ (N : ℝ) ^ 2) (h11 : (N : ℝ) ^ 11 ≤ t ^ 7) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 384 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  set lam := t / (8 * Real.pi * (N : ℝ) ^ 3) with hlamd
  have hlam1 : lam ≤ 1 := by
    rw [hlamd, div_le_one (by positivity)]
    have : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    nlinarith
  have hlam0 : 0 < lam := by positivity
  set P := 128 * N * lam ^ (1 / 6 : ℝ) + 128 * Real.sqrt N / lam ^ (1 / 6 : ℝ) with hP
  have hblk := block_of_prefix (σ := 11 / 18) (t := t) (by norm_num) hN (P := P) (by positivity)
    (fun L hL1 hLN => by
      refine (dirichlet_block_bound_third_sharp ht0 hN hL1 (by omega) hlam1).trans ?_
      have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
      have hs : Real.sqrt L ≤ Real.sqrt N := Real.sqrt_le_sqrt hLN'
      rw [hP]
      gcongr)
  refine hblk.trans ?_
  have hlN : 11 * Real.log (N : ℝ) ≤ 7 * Real.log t := by
    have := Real.log_le_log (by positivity) h11
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hlt2 : Real.log t ≤ 2 * Real.log (N : ℝ) := by
    have := Real.log_le_log ht0 h2
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hs : 0 < t * (N : ℝ) ^ 3 := by positivity
  have hlup : lam ≤ t / (N : ℝ) ^ 3 := by
    rw [hlamd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hpi) hs]
  have hllo : t / (26 * (N : ℝ) ^ 3) ≤ lam := by
    rw [hlamd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hpi4) hs]
  have hA : (N : ℝ) * lam ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)) ≤ t ^ (1 / 9 : ℝ) := by
    have h1 : lam ^ (1 / 6 : ℝ) ≤ (t / (N : ℝ) ^ 3) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow hlam0.le hlup (by norm_num)
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hN0.le)
      (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow hN0, Real.log_rpow ht0,
      Real.log_div ht0.ne' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hB : Real.sqrt N / lam ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))
      ≤ 2 * t ^ (1 / 9 : ℝ) := by
    have h1 : (t / (26 * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) ≤ lam ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hllo (by norm_num)
    have h2' : Real.sqrt N / lam ^ (1 / 6 : ℝ) ≤ Real.sqrt N / (t / (26 * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) h1
    refine (mul_le_mul_of_nonneg_right h2' (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    have h26 : Real.log 26 ≤ 5 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.sqrt_eq_rpow, Real.log_rpow hN0, Real.log_rpow (by positivity),
      Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_rpow hN0, Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow ht0]
    push_cast
    nlinarith
  have e : P * (N : ℝ) ^ (-(11 / 18 : ℝ))
      = 128 * ((N : ℝ) * lam ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)))
        + 128 * (Real.sqrt N / lam ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))) := by
    rw [hP]; ring
  rw [e]
  linarith

/-- **Second-derivative block.**  For `t⁷ ≤ N¹¹` and `N ≤ t`: `≤ 2304 t^{1/9}`. -/
theorem norm_eeBlock_le_second {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (h11 : t ^ 7 ≤ (N : ℝ) ^ 11) (hNt : (N : ℝ) ≤ t) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2304 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  have hlN : 7 * Real.log t ≤ 11 * Real.log (N : ℝ) := by
    have := Real.log_le_log (by positivity) h11
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hlNt : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hN0 hNt
  have hlN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlamEq : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2
      = t / (8 * Real.pi * (N : ℝ) ^ 2) := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]; norm_num; field_simp; ring
  have ht2 : t ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by
    have h1 : t ^ 7 ≤ ((N : ℝ) ^ 2) ^ 7 := by
      calc t ^ 7 ≤ (N : ℝ) ^ 11 := h11
        _ ≤ (N : ℝ) ^ 14 := pow_le_pow_right₀ hN1 (by norm_num)
        _ = ((N : ℝ) ^ 2) ^ 7 := by ring
    have := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    nlinarith [sq_nonneg (N : ℝ)]
  have hlam1 : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2 ≤ 1 := by
    rw [hlamEq, div_le_one (by positivity)]; exact ht2
  have h := dirichlet_block_sigma_full (σ := 11 / 18) (by norm_num) t ht0 2 N (2 * N) le_rfl hN
    (by omega) (by omega) hlam1
  rw [hlamEq, show 2 * N - N = N by omega] at h
  refine h.trans ?_
  set lam := t / (8 * Real.pi * (N : ℝ) ^ 2) with hlamd
  have hlam0 : 0 < lam := by positivity
  have e1 : (1 / ((2 : ℝ) ^ 2 - 2)) = 1 / 2 := by norm_num
  have e2 : (1 - 4 / (2 : ℝ) ^ 2) = 0 := by norm_num
  have e3 : (-(2 / (2 : ℝ) ^ 2)) = -(1 / 2) := by norm_num
  rw [e1, e2, e3, Real.rpow_zero, one_mul]
  have hA : (N : ℝ) * ((4 : ℝ) ^ 2 * lam) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))
      ≤ t ^ (1 / 9 : ℝ) := by
    have h1 : ((4 : ℝ) ^ 2 * lam) ^ (1 / 2 : ℝ) ≤ (t / (N : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have hs : 0 < t * (N : ℝ) ^ 2 := by positivity
      rw [hlamd, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (sub_pos.mpr hpi) hs]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hN0.le)
      (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow hN0, Real.log_rpow ht0,
      Real.log_div ht0.ne' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hB : lam ^ (-(1 / 2) : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)) ≤ 8 * t ^ (1 / 9 : ℝ) := by
    have hllo : t / (26 * (N : ℝ) ^ 2) ≤ lam := by
      have hs : 0 < t * (N : ℝ) ^ 2 := by positivity
      rw [hlamd, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (sub_pos.mpr hpi4) hs]
    have h1 : lam ^ (-(1 / 2) : ℝ) ≤ (t / (26 * (N : ℝ) ^ 2)) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hllo (by norm_num)
    refine (mul_le_mul_of_nonneg_right h1 (by positivity)).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    have h26 : Real.log 26 ≤ 5 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow hN0, Real.log_rpow ht0,
      Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    nlinarith
  have e : 256 * ((N : ℝ) * ((4 : ℝ) ^ 2 * lam) ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2) : ℝ))
      * (N : ℝ) ^ (-(11 / 18 : ℝ))
      = 256 * ((N : ℝ) * ((4 : ℝ) ^ 2 * lam) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))
        + lam ^ (-(1 / 2) : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ))) := by ring
  rw [e]
  linarith

/-- **Kuzmin–Landau block.**  For `3t ≤ 4πN` and `N⁷ ≤ 10⁷ t¹⁶`: `≤ 100 t^{1/9}`. -/
theorem norm_eeBlock_le_kuzminLandau {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (htN : 3 * t ≤ 4 * Real.pi * N) (hup : (N : ℝ) ^ 7 ≤ 10 ^ 7 * t ^ 16) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 100 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  have hblk : ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (6 * Real.pi * N / t + 1) * (N : ℝ) ^ (-(11 / 18 : ℝ)) := by
    refine dirichlet_block_sigma_bound (by norm_num) t N (2 * N) hN (by omega) _ ?_
    intro m hm1 hm2
    have hP : 0 ≤ 6 * Real.pi * N / t + 1 := by positivity
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]; exact hP
    · rw [Finset.sum_Ico_eq_sum_range]
      have h := norm_logPhase_dyadic_prefix_le_kuzminLandau t ht0 N (m - N) hN (by omega)
        (by omega) htN
      refine le_of_eq_of_le ?_ h
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natCast_cpow_neg_I_mul t (N + j) (by omega)]
      push_cast
      ring_nf
  refine hblk.trans ?_
  have hlup : 7 * Real.log (N : ℝ) ≤ 7 * Real.log 10 + 16 * Real.log t := by
    have := Real.log_le_log (by positivity) hup
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      at this
    push_cast at this; linarith
  have hl10 : Real.log 10 ≤ 4 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  -- `N^{7/18} ≤ 4t`
  have h718 : (N : ℝ) ^ (7 / 18 : ℝ) ≤ 4 * t := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_rpow hN0, Real.log_mul (by norm_num) ht0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    linarith
  have hsplit : (6 * Real.pi * N / t + 1) * (N : ℝ) ^ (-(11 / 18 : ℝ))
      = 6 * Real.pi * ((N : ℝ) ^ (7 / 18 : ℝ) / t) + (N : ℝ) ^ (-(11 / 18 : ℝ)) := by
    have e : (N : ℝ) * (N : ℝ) ^ (-(11 / 18 : ℝ)) = (N : ℝ) ^ (7 / 18 : ℝ) := by
      rw [← Real.rpow_one_add' hN0.le (by norm_num)]; norm_num
    rw [← e]; field_simp
  rw [hsplit]
  have h1 : (N : ℝ) ^ (7 / 18 : ℝ) / t ≤ 4 := by rw [div_le_iff₀ ht0]; linarith
  have h2 : (N : ℝ) ^ (-(11 / 18 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have h3 : (1 : ℝ) ≤ t ^ (1 / 9 : ℝ) := Real.one_le_rpow ht (by norm_num)
  nlinarith

/-! ## Every dyadic block -/

/-- **Every dyadic block at `σ = 11/18`**, for `1024π ≤ t` and `t² ≤ N⁷ ≤ 10⁷t¹⁶`. -/
theorem norm_eeBlock_le {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (hlow : t ^ 2 ≤ (N : ℝ) ^ 7) (hup : (N : ℝ) ^ 7 ≤ 10 ^ 7 * t ^ 16) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 10 ^ 6 * t ^ (1 / 9 : ℝ) := by
  have hpi := Real.pi_gt_three
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h19 : (1 : ℝ) ≤ t ^ (1 / 9 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  by_cases hkl : 3 * t ≤ 4 * Real.pi * N
  · exact (norm_eeBlock_le_kuzminLandau ht1 hN hkl hup).trans (by nlinarith)
  push Not at hkl
  have hNt : (N : ℝ) ≤ t := by nlinarith
  by_cases h7 : t ^ 7 ≤ (N : ℝ) ^ 11
  · exact (norm_eeBlock_le_second ht1 hN h7 hNt).trans (by nlinarith)
  push Not at h7
  by_cases h2 : t ≤ (N : ℝ) ^ 2
  · exact (norm_eeBlock_le_third ht1 hN h2 h7.le).trans (by nlinarith)
  push Not at h2
  by_cases h5 : t ^ 5 ≤ (N : ℝ) ^ 13
  · exact norm_eeBlock_le_B ht hN h5 h2.le
  push Not at h5
  have hN4 : t ≤ (N : ℝ) ^ 4 := by
    have h28 : t ^ 7 ≤ ((N : ℝ) ^ 4) ^ 7 :=
      calc t ^ 7 ≤ t ^ 8 := pow_le_pow_right₀ ht1 (by norm_num)
        _ = (t ^ 2) ^ 4 := by ring
        _ ≤ ((N : ℝ) ^ 7) ^ 4 := pow_le_pow_left₀ (by positivity) hlow 4
        _ = ((N : ℝ) ^ 4) ^ 7 := by ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h28
  have hlam : 3 * t ≤ 16 * Real.pi * (N : ℝ) ^ 4 := by nlinarith
  exact (norm_eeBlock_le_fourth ht1 hN hlam h5.le).trans (by nlinarith)

/-- `Nat.log 2 m ≤ log m / log 2`. -/
theorem natLog_two_le_ee {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2, ← Real.log_rpow (by norm_num)]
  refine Real.log_le_log (by positivity) ?_
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

/-- Comparing `k`-th powers. -/
theorem ee_le_of_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) (hk : k ≠ 0)
    (h : a ^ k ≤ b ^ k) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb hk).mp h

theorem neg_elevenEighteenths_add_eq (t : ℝ) :
    -((11 / 18 : ℂ) + (t : ℂ) * Complex.I) = -(((11 / 18 : ℝ)) : ℂ) - Complex.I * (t : ℂ) := by
  push_cast; ring

/-! ## The cut points -/

/-- The lower cut `c = ⌈t^{2/7}⌉ + 3`: `t^{2/7} ≤ c ≤ 5t^{2/7}`. -/
theorem ee_cut_c {t : ℝ} (ht : 1 ≤ t) {c : ℕ} (hc : c = ⌈t ^ (2 / 7 : ℝ)⌉₊ + 3) :
    3 ≤ c ∧ t ^ (2 / 7 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ t ^ (2 / 7 : ℝ) + 4
      ∧ (c : ℝ) ^ 7 ≤ 78125 * t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hq : (t ^ (2 / 7 : ℝ)) ^ 7 = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have ht27 : (1 : ℝ) ≤ t ^ (2 / 7 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hcR : t ^ (2 / 7 : ℝ) ≤ (c : ℝ) := by
    have := Nat.le_ceil (t ^ (2 / 7 : ℝ)); rw [hc]; push_cast; linarith
  have hcR'' : (c : ℝ) ≤ t ^ (2 / 7 : ℝ) + 4 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ t ^ (2 / 7 : ℝ) by positivity)
    rw [hc]; push_cast; linarith
  have hcR' : (c : ℝ) ≤ 5 * t ^ (2 / 7 : ℝ) := by linarith
  have hc7 : (c : ℝ) ^ 7 ≤ 78125 * t ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hcR' 7
    rw [mul_pow, hq] at this; linarith
  exact ⟨by omega, hcR, hcR'', hc7⟩

/-- The upper cut `2^R`, `R = ⌊log₂⌈t²⌉⌋ + 1`: `t² < 2^R ≤ 4t²` and `R ≤ 4 log t`. -/
theorem ee_cut_R {t : ℝ} (ht : 8 ≤ t) {R : ℕ} (hR : R = Nat.log 2 ⌈t ^ 2⌉₊ + 1) :
    t ^ 2 < (2 : ℝ) ^ R ∧ (2 : ℝ) ^ R ≤ 4 * t ^ 2 ∧ (R : ℝ) ≤ 4 * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hceil1 : 1 ≤ ⌈t ^ 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have h2R : t ^ 2 < (2 : ℝ) ^ R := by
    have h1 : ⌈t ^ 2⌉₊ < 2 ^ R := by
      rw [hR]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : t ^ 2 ≤ (⌈t ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈t ^ 2⌉₊ : ℝ) < ((2 ^ R : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3; linarith
  have hceil2 : (⌈t ^ 2⌉₊ : ℝ) ≤ 2 * t ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ t ^ 2 by positivity); nlinarith
  have h2R' : (2 : ℝ) ^ R ≤ 4 * t ^ 2 := by
    rw [hR, pow_succ]
    have h1 := Nat.pow_log_le_self 2 (show ⌈t ^ 2⌉₊ ≠ 0 by omega)
    have h3 : ((2 ^ Nat.log 2 ⌈t ^ 2⌉₊ : ℕ) : ℝ) ≤ (⌈t ^ 2⌉₊ : ℝ) := by exact_mod_cast h1
    push_cast at h3; linarith
  have hlog2 : 2 ≤ Real.log t := by
    have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have : (2 : ℝ) ≤ Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast; linarith
    linarith
  have hRlog : (R : ℝ) ≤ 4 * Real.log t := by
    have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hnl := natLog_two_le_ee hceil1
    have hlogc : Real.log (⌈t ^ 2⌉₊ : ℝ) ≤ Real.log 2 + 2 * Real.log t := by
      rw [← Real.log_rpow ht0, ← Real.log_mul (by norm_num) (by positivity)]
      refine Real.log_le_log (by exact_mod_cast hceil1) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; linarith
    have hdiv : Real.log (⌈t ^ 2⌉₊ : ℝ) / Real.log 2 ≤ 1 + 3 * Real.log t := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ Real.log t := by linarith
      nlinarith
    rw [hR]; push_cast; linarith
  exact ⟨h2R, h2R', hRlog⟩

/-! ## Blocks, head and tails -/

/-- All dyadic blocks between the cuts. -/
theorem ee_blocks {t : ℝ} (ht : 1024 * Real.pi ≤ t) {c R : ℕ}
    (hcR : t ^ (2 / 7 : ℝ) ≤ (c : ℝ)) (hc2R7 : ((c : ℝ) * 2 ^ R) ^ 7 ≤ 1280000000 * t ^ 16) :
    ∀ r < R, ‖∑ n ∈ Finset.Ico (c * 2 ^ r) (c * 2 ^ (r + 1)),
      (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤ 10 ^ 6 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith [Real.pi_pos]
  have hq : (t ^ (2 / 7 : ℝ)) ^ 7 = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hc1 : (1 : ℝ) ≤ c :=
    le_trans (Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by norm_num)) hcR
  intro r hr
  have hN1 : 1 ≤ c * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by
    have : c ≠ 0 := by intro h; rw [h] at hc1; norm_num at hc1
    positivity)
  have hblk : c * 2 ^ (r + 1) = 2 * (c * 2 ^ r) := by rw [pow_succ]; ring
  rw [hblk]
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hc0 : (0 : ℝ) ≤ c := by positivity
  refine norm_eeBlock_le ht hN1 ?_ ?_
  · have hcN : (c : ℝ) ≤ ((c * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right hc0 h2r
    have := pow_le_pow_left₀ (by positivity) (hcR.trans hcN) 7
    rw [hq] at this; exact this
  · have hr2 : 2 * ((c * 2 ^ r : ℕ) : ℝ) ≤ (c : ℝ) * 2 ^ R := by
      push_cast
      have : (2 : ℝ) ^ r * 2 ≤ 2 ^ R := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have h128 : (2 * ((c * 2 ^ r : ℕ) : ℝ)) ^ 7 ≤ ((c : ℝ) * 2 ^ R) ^ 7 :=
      pow_le_pow_left₀ (by positivity) hr2 7
    have : (2 * ((c * 2 ^ r : ℕ) : ℝ)) ^ 7 = 128 * ((c * 2 ^ r : ℕ) : ℝ) ^ 7 := by ring
    rw [this] at h128
    linarith

/-- The head `Σ_{n<c} n^{−11/18}` is `≤ 8t^{1/9}`. -/
theorem ee_head {t : ℝ} (ht : 1 ≤ t) {c : ℕ} (hc3 : 3 ≤ c)
    (hcR'' : (c : ℝ) ≤ t ^ (2 / 7 : ℝ) + 4) :
    1 + (((c - 1 : ℕ) : ℝ) ^ (1 - 11 / 18 : ℝ) - 1) / (1 - 11 / 18)
      + ((c - 1 : ℕ) : ℝ) ^ (-(11 / 18 : ℝ)) ≤ 8 * t ^ (1 / 9 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hq : (t ^ (2 / 7 : ℝ)) ^ 7 = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have ht27 : (1 : ℝ) ≤ t ^ (2 / 7 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have h19 : (1 : ℝ) ≤ t ^ (1 / 9 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hc1 : (1 : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by
    have : 1 ≤ c - 1 := by omega
    exact_mod_cast this
  have hcle : ((c - 1 : ℕ) : ℝ) ≤ 4 * t ^ (2 / 7 : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hneg : ((c - 1 : ℕ) : ℝ) ^ (-(11 / 18 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have e : (1 - 11 / 18 : ℝ) = 7 / 18 := by norm_num
  rw [e]
  have h718 : ((c - 1 : ℕ) : ℝ) ^ (7 / 18 : ℝ) ≤ 2 * t ^ (1 / 9 : ℝ) := by
    refine ee_le_of_pow_le (by positivity) (by positivity) 18 (by norm_num) ?_
    have hk : (((c - 1 : ℕ) : ℝ) ^ (7 / 18 : ℝ)) ^ 18 = ((c - 1 : ℕ) : ℝ) ^ 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hkt : (t ^ (1 / 9 : ℝ)) ^ 18 = t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    rw [hk, mul_pow, hkt]
    have h4 := pow_le_pow_left₀ (by positivity) hcle 7
    rw [mul_pow, hq] at h4
    have h16 : (4 : ℝ) ^ 7 ≤ 2 ^ 18 := by norm_num
    exact h4.trans (mul_le_mul_of_nonneg_right h16 (by positivity))
  have : (((c - 1 : ℕ) : ℝ) ^ (7 / 18 : ℝ) - 1) / (7 / 18)
      = 18 / 7 * ((c - 1 : ℕ) : ℝ) ^ (7 / 18 : ℝ) - 18 / 7 := by ring
  rw [this]
  linarith

/-- The two truncation tails are each `≤ 4`. -/
theorem ee_tails {t : ℝ} (ht : 1 ≤ t) {K : ℕ} (hKlow : t ^ 2 ≤ (K : ℝ))
    (hK7 : (K : ℝ) ^ 7 ≤ 1280000000 * t ^ 16) {w : ℂ} (hwim : w.im = t) (hwre : w.re = 11 / 18) :
    (K : ℝ) ^ (1 - 11 / 18 : ℝ) / ‖w - 1‖ ≤ 4
      ∧ ‖w‖ * ((K : ℝ) ^ (-(11 / 18 : ℝ)) / (11 / 18)) ≤ 4 := by
  have ht0 : 0 < t := by linarith
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hKlow
  constructor
  · have hnorm : t ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, hwim, Complex.one_im, sub_zero, abs_of_pos ht0] at this
      exact this
    have hpos : 0 < ‖w - 1‖ := lt_of_lt_of_le ht0 hnorm
    rw [div_le_iff₀ hpos]
    have hK718 : (K : ℝ) ^ (1 - 11 / 18 : ℝ) ≤ 4 * t := by
      refine ee_le_of_pow_le (by positivity) (by positivity) 18 (by norm_num) ?_
      have hk : ((K : ℝ) ^ (1 - 11 / 18 : ℝ)) ^ 18 = (K : ℝ) ^ 7 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; norm_num
      rw [hk, mul_pow]
      have h1618 : t ^ 16 ≤ t ^ 18 := pow_le_pow_right₀ ht (by norm_num)
      have hc : (1280000000 : ℝ) ≤ 4 ^ 18 := by norm_num
      calc (K : ℝ) ^ 7 ≤ 1280000000 * t ^ 16 := hK7
        _ ≤ 1280000000 * t ^ 18 := mul_le_mul_of_nonneg_left h1618 (by norm_num)
        _ ≤ 4 ^ 18 * t ^ 18 := mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  · have hwn : ‖w‖ ≤ 2 * t := by
      have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      rw [hwre, hwim, abs_of_pos ht0] at h1
      norm_num at h1
      linarith
    have hKn : (K : ℝ) ^ (-(11 / 18 : ℝ)) ≤ t⁻¹ := by
      rw [Real.rpow_neg hK0.le]
      refine inv_anti₀ ht0 ?_
      refine ee_le_of_pow_le ht0.le (by positivity) 18 (by norm_num) ?_
      have hk : ((K : ℝ) ^ (11 / 18 : ℝ)) ^ 18 = (K : ℝ) ^ 11 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; norm_num
      rw [hk]
      calc t ^ 18 ≤ t ^ 22 := pow_le_pow_right₀ ht (by norm_num)
        _ = (t ^ 2) ^ 11 := by ring
        _ ≤ (K : ℝ) ^ 11 := pow_le_pow_left₀ (by positivity) hKlow 11
    calc ‖w‖ * ((K : ℝ) ^ (-(11 / 18 : ℝ)) / (11 / 18)) ≤ (2 * t) * (t⁻¹ / (11 / 18)) := by
          gcongr
      _ = 36 / 11 := by field_simp; ring
      _ ≤ 4 := by norm_num

/-- **`ζ` on the line `Re s = 11/18`.**  `‖ζ(11/18 + it)‖ ≤ 10⁷ t^{1/9} log t` for `t ≥ 1024π`. -/
theorem norm_riemannZeta_elevenEighteenths_le {t : ℝ} (ht : 1024 * Real.pi ≤ t) :
    ‖riemannZeta ((11 / 18 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 10 ^ 7 * t ^ (1 / 9 : ℝ) * Real.log t := by
  have hpi := Real.pi_gt_three
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht8 : 8 ≤ t := by linarith
  have h19 : (1 : ℝ) ≤ t ^ (1 / 9 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈t ^ (2 / 7 : ℝ)⌉₊ + 3 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = Nat.log 2 ⌈t ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨hc3, hcR, hcR'', hc7⟩ := ee_cut_c ht1 hc
  obtain ⟨h2R, h2R', hRlog⟩ := ee_cut_R ht8 hR
  have hlog2 : 2 ≤ Real.log t := by
    have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht8
    have : (2 : ℝ) ≤ Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast; linarith
    linarith
  have hc2R7 : ((c : ℝ) * 2 ^ R) ^ 7 ≤ 1280000000 * t ^ 16 := by
    have h2R7 : ((2 : ℝ) ^ R) ^ 7 ≤ 16384 * t ^ 14 := by
      have := pow_le_pow_left₀ (by positivity) h2R' 7
      calc ((2 : ℝ) ^ R) ^ 7 ≤ (4 * t ^ 2) ^ 7 := this
        _ = 16384 * t ^ 14 := by ring
    rw [mul_pow]
    calc (c : ℝ) ^ 7 * ((2 : ℝ) ^ R) ^ 7 ≤ (78125 * t ^ 2) * (16384 * t ^ 14) :=
          mul_le_mul hc7 h2R7 (by positivity) (by positivity)
      _ = 1280000000 * t ^ 16 := by ring
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = c * 2 ^ R - 1 := ⟨_, rfl⟩
  have hcR2 : (3 : ℝ) * 2 ^ R ≤ (c : ℝ) * 2 ^ R := by
    have : (3 : ℝ) ≤ c := by exact_mod_cast hc3
    gcongr
  have hKR : (K : ℝ) = (c : ℝ) * 2 ^ R - 1 := by
    rw [hK, Nat.cast_sub (by
      have : 1 ≤ 2 ^ R := Nat.one_le_two_pow
      nlinarith)]
    push_cast; ring
  have hKlow : t ^ 2 ≤ (K : ℝ) := by rw [hKR]; nlinarith
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by nlinarith
    exact_mod_cast this
  have hK7 : (K : ℝ) ^ 7 ≤ 1280000000 * t ^ 16 := by
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have : (K : ℝ) ≤ (c : ℝ) * 2 ^ R := by rw [hKR]; linarith
    exact le_trans (pow_le_pow_left₀ hK0 this 7) hc2R7
  have hbound := ee_blocks ht hcR hc2R7
  have hhead := ee_head ht1 hc3 hcR''
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (11 / 18 : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = 11 / 18 := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  obtain ⟨htail1, htail2⟩ := ee_tails ht1 hKlow hK7 hwim hwre
  have htrunc := norm_riemannZeta_le_partialSum (w := w) (by rw [hwre]; norm_num) hw1 hK1
  rw [hwre] at htrunc
  have hsum : ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) : ℂ) ^ (-w)
      = ∑ n ∈ Finset.Ico 1 (c * 2 ^ R), (n : ℂ) ^ (-((11 / 18 : ℝ) : ℂ) - Complex.I * (t : ℂ)) := by
    have hIco : Finset.Ico 1 (c * 2 ^ R) = Finset.Icc 1 K := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_Icc, hK]; omega
    rw [hIco]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hw, Complex.ofReal_natCast, neg_elevenEighteenths_add_eq]
  rw [hsum] at htrunc
  have hσ0 : (0 : ℝ) < 11 / 18 := by norm_num
  have hσ1 : (11 / 18 : ℝ) < 1 := by norm_num
  have hblocks := norm_dirichlet_sigma_partial_of_blockBound (σ := 11 / 18) (t := t)
    hσ0 hσ1 hc3 (fun _ => 10 ^ 6 * t ^ (1 / 9 : ℝ)) (R := R) hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hblocks
  have hR' : (R : ℝ) * (10 ^ 6 * t ^ (1 / 9 : ℝ)) ≤ 4 * Real.log t * (10 ^ 6 * t ^ (1 / 9 : ℝ)) :=
    mul_le_mul_of_nonneg_right hRlog (by positivity)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t ^ (1 / 9 : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log t := ⟨_, rfl⟩
  rw [← hu] at hblocks hhead hR' h19 ⊢
  rw [← hL] at hR' hlog2 ⊢
  have hk : u * 2 ≤ u * L := mul_le_mul_of_nonneg_left hlog2 (by linarith)
  have e1 : 4 * L * (10 ^ 6 * u) = 4000000 * (u * L) := by ring
  have e2 : 10 ^ 7 * u * L = 10000000 * (u * L) := by ring
  rw [e1] at hR'
  rw [e2]
  linarith only [htrunc, hblocks, hhead, htail1, htail2, hR', hk, h19]

end

end RHTower
