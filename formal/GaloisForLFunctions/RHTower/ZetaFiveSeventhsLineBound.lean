import GaloisForLFunctions.RHTower.ZetaCriticalLineWeylBound
import GaloisForLFunctions.RHTower.Sieve.FourthDerivativeTestSharp

/-!
# `ζ` on the line `Re s = 5/7`: the exponent `1/14`

For `t ≥ 8`, `‖ζ(5/7 + it)‖ ≤ 7300 · t^{1/14} · log t` (`norm_riemannZeta_fiveSevenths_le`).
This is the order-four point `μ(1 − l/(2L−2)) ≤ 1/(2L−2)`, `l = 4`, `L = 8`, of the
van der Corput hierarchy, one step past Weyl's `μ(½) ≤ 1/6`.

Proof.  Truncate at `K ≥ t²` (`norm_riemannZeta_le_partialSum`), take absolute values below
`c = ⌈t^{1/4}⌉ + 3`, and bound the dyadic blocks `[N, 2N)` of `n^{−5/7−it}` after partial summation.
Each regime is reduced to a polynomial inequality by raising both sides to a suitable integer power:

* `3t ≤ 4πN`: Kuzmin–Landau, `(6πN/t + 1) N^{−5/7} ≤ 40`;
* `t³ ≤ N⁵`: the second-derivative test, `256(4N^{2/7}λ^{1/2} + λ^{−1/2}N^{−5/7}) ≤ 2560 t^{1/14}`;
* `t⁴ ≤ N⁹ < t^{27/5}`: the sharp third-derivative test, `≤ 384 t^{1/14}`;
* `N⁹ < t⁴`, `t ≤ N⁴`: the sharp fourth-derivative test (`fourth_derivative_test_sharp`) with
  `λ = 3t/(16πN⁴)`, `224(N^{2/7}λ^{1/14} + N^{1/28}λ^{−1/14}) ≤ 672 t^{1/14}`.

The head is at most `6t^{1/14}`, the tails at most `6`, and there are at most `4 log t` blocks.
-/

namespace RHTower

open RHTower.Sieve Finset Complex

noncomputable section

private theorem rpow_pow_fs {x : ℝ} (hx : 0 ≤ x) (p : ℝ) (k : ℕ) :
    (x ^ p) ^ k = x ^ (p * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-! ## Block bounds -/

/-- **Kuzmin–Landau block** at `σ = 5/7`. -/
theorem norm_fsBlock_le_kuzminLandau {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N)
    (htN : 3 * t ≤ 4 * Real.pi * N) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (6 * Real.pi * N / t + 1) * (N : ℝ) ^ (-(5 / 7 : ℝ)) := by
  refine dirichlet_block_sigma_bound (by norm_num) t N (2 * N) hN (by omega) _ ?_
  intro m hm1 hm2
  have hP : 0 ≤ 6 * Real.pi * N / t + 1 := by positivity
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]; exact hP
  · rw [Finset.sum_Ico_eq_sum_range]
    have h := norm_logPhase_dyadic_prefix_le_kuzminLandau t ht N (m - N) hN (by omega)
      (by omega) htN
    refine le_of_eq_of_le ?_ h
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [natCast_cpow_neg_I_mul t (N + j) (by omega)]
    push_cast
    ring_nf

/-- **Second-derivative block** at `σ = 5/7`, for `t ≤ 8πN²`. -/
theorem norm_fsBlock_le_second {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N)
    (hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 256 * ((N : ℝ) * (16 * (t / (8 * Real.pi * (N : ℝ) ^ 2))) ^ (1 / 2 : ℝ)
          + (t / (8 * Real.pi * (N : ℝ) ^ 2)) ^ (-(1 / 2 : ℝ))) * (N : ℝ) ^ (-(5 / 7 : ℝ)) := by
  have hlamEq : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2
      = t / (8 * Real.pi * (N : ℝ) ^ 2) := by
    simp only [Nat.factorial, Nat.succ_eq_add_one]; norm_num; field_simp; ring
  have hlam1 : t / (2 * Real.pi) * (Nat.factorial (2 - 1) : ℝ) / (2 * (N : ℝ)) ^ 2 ≤ 1 := by
    rw [hlamEq, div_le_one (by positivity)]; exact hlam
  have h := dirichlet_block_sigma_full (σ := 5 / 7) (by norm_num) t ht 2 N (2 * N) le_rfl hN
    (by omega) (by omega) hlam1
  rw [hlamEq, show 2 * N - N = N by omega] at h
  refine h.trans (le_of_eq ?_)
  norm_num

/-- **Sharp third-derivative block** at `σ = 5/7`, for `t ≤ 8πN³`. -/
theorem norm_fsBlock_le_third_sharp {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N)
    (hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (128 * N * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ)
        + 128 * Real.sqrt N / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ))
          * (N : ℝ) ^ (-(5 / 7 : ℝ)) := by
  have hlam1 : t / (8 * Real.pi * (N : ℝ) ^ 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hlam
  refine dirichlet_block_sigma_bound (by norm_num) t N (2 * N) hN (by omega) _ ?_
  intro m hm1 hm2
  have hP : 0 ≤ 128 * N * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ)
      + 128 * Real.sqrt N / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) := by positivity
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]; exact hP
  · rw [Finset.sum_Ico_eq_sum_range]
    have h := dirichlet_block_bound_third_sharp ht (L := m - N) hN (by omega) (by omega) hlam1
    refine h.trans ?_
    have hmN : ((m - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show m - N ≤ N by omega)
    have hs : Real.sqrt ((m - N : ℕ) : ℝ) ≤ Real.sqrt N := Real.sqrt_le_sqrt hmN
    gcongr

/-- **The sharp fourth-derivative block bound for `∑ n^{−it}`.**  With `λ = 3t/(16πN⁴) ≤ 1`, a run
of `L` consecutive Dirichlet phases from `N` inside `[N, 2N]` is at most
`224(L λ^{1/14} + L^{3/4} λ^{−1/14})`. -/
theorem dirichlet_block_bound_fourth_sharp {t : ℝ} (ht : 0 < t) {N L : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1) (hlam1 : 3 * t / (16 * Real.pi * (N : ℝ) ^ 4) ≤ 1) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 224 * ((L : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (1 / 14 : ℝ)
        + (L : ℝ) ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (-(1 / 14 : ℝ))) := by
  have hπ := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = 3 * t / (16 * Real.pi * (N : ℝ) ^ 4) := ⟨_, rfl⟩
  rw [← hlamdef] at hlam1 ⊢
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlo_eq : t / (2 * Real.pi) * (Nat.factorial 3 : ℝ) * ((2 * (N : ℝ)) ^ (3 + 1))⁻¹ = lam := by
    rw [hlamdef]; simp only [Nat.factorial]; push_cast; field_simp; ring
  have hhi_eq : t / (2 * Real.pi) * (Nat.factorial 3 : ℝ) * (((N : ℝ)) ^ (3 + 1))⁻¹ = 16 * lam := by
    rw [hlamdef]; simp only [Nat.factorial]; push_cast; field_simp; ring
  have hspan_mem : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      0 < x ∧ x ∈ Set.Icc ((N : ℝ)) (2 * (N : ℝ)) := by
    intro x hx
    have hL1 : ((L - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : L - 1 ≤ N := by omega
      exact_mod_cast this
    exact ⟨by linarith [hx.1], hx.1, by linarith [hx.2]⟩
  have hphase : ∀ i ∈ Finset.range L, ((N + i : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + i) : ℝ) : ℂ) * Complex.I) := by
    intro i _
    have harg : ((N + i : ℕ) : ℝ) = (N : ℝ) + (i : ℝ) := by push_cast; ring
    rw [natCast_cpow_neg_I_mul t (N + i) (by omega), harg]
  rw [Finset.sum_congr rfl hphase]
  have hpos4 : ((-1 : ℝ)) ^ (3 + 1) = 1 := by norm_num
  have hchain : ∀ i < 4, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      HasDerivAt (fun y => logPhaseChain t i y) (logPhaseChain t (i + 1) x) x :=
    fun i _ x hx => logPhaseChain_hasDerivAt t i (hspan_mem x hx).1
  have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)), lam ≤ logPhaseChain t 4 x := by
    intro x hx
    have hb := (logPhaseChain_signed_bounds t ht 3 (lt_of_lt_of_le one_pos hN1)
      (hspan_mem x hx).2).1
    rw [hpos4, one_mul, hlo_eq] at hb
    exact hb
  have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      logPhaseChain t 4 x ≤ 16 * lam := by
    intro x hx
    have hb := (logPhaseChain_signed_bounds t ht 3 (lt_of_lt_of_le one_pos hN1)
      (hspan_mem x hx).2).2
    rw [hpos4, one_mul, hhi_eq] at hb
    exact hb
  have hD := fourth_derivative_test_sharp (fun i y => logPhaseChain t i y) (N : ℝ) L hL
    hlam0 hlam1 (by norm_num) hchain hlo hhi
  refine hD.trans (le_of_eq ?_)
  ring

/-- **Sharp fourth-derivative block** at `σ = 5/7`, for `3t ≤ 16πN⁴`. -/
theorem norm_fsBlock_le_fourth_sharp {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N)
    (hlam : 3 * t ≤ 16 * Real.pi * (N : ℝ) ^ 4) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 224 * ((N : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (1 / 14 : ℝ)
        + (N : ℝ) ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (-(1 / 14 : ℝ)))
          * (N : ℝ) ^ (-(5 / 7 : ℝ)) := by
  have hlam1 : 3 * t / (16 * Real.pi * (N : ℝ) ^ 4) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hlam
  refine dirichlet_block_sigma_bound (by norm_num) t N (2 * N) hN (by omega) _ ?_
  intro m hm1 hm2
  have hP : 0 ≤ 224 * ((N : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (1 / 14 : ℝ)
      + (N : ℝ) ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * (N : ℝ) ^ 4)) ^ (-(1 / 14 : ℝ))) := by
    positivity
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty, norm_zero]; exact hP
  · rw [Finset.sum_Ico_eq_sum_range]
    have h := dirichlet_block_bound_fourth_sharp ht (L := m - N) hN (by omega) (by omega) hlam1
    refine h.trans ?_
    have hmN : ((m - N : ℕ) : ℝ) ≤ N := by exact_mod_cast (show m - N ≤ N by omega)
    have hs : ((m - N : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hmN (by norm_num)
    gcongr

/-! ## The four regimes, numerically -/

/-- Comparing `k`-th powers. -/
private theorem fs_le_of_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) (hk : k ≠ 0)
    (h : a ^ k ≤ b ^ k) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb hk).mp h

/-- Removing the weight: `P ≤ Q N^{5/7}` gives `P N^{−5/7} ≤ Q`. -/
private theorem fs_weight_le {P Q N : ℝ} (hN : 0 < N) (h : P ≤ Q * N ^ (5 / 7 : ℝ)) :
    P * N ^ (-(5 / 7 : ℝ)) ≤ Q := by
  have h1 : N ^ (5 / 7 : ℝ) * N ^ (-(5 / 7 : ℝ)) = 1 := by
    rw [← Real.rpow_add hN]; norm_num
  calc P * N ^ (-(5 / 7 : ℝ)) ≤ Q * N ^ (5 / 7 : ℝ) * N ^ (-(5 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = Q := by rw [mul_assoc, h1, mul_one]

theorem fsBlock_kl_num {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N) (hNup : N ^ 4 ≤ 10 ^ 4 * t ^ 9) :
    (6 * Real.pi * N / t + 1) * N ^ (-(5 / 7 : ℝ)) ≤ 40 * t ^ (1 / 14 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have h15 : (1 : ℝ) ≤ t ^ (1 / 14 : ℝ) := Real.one_le_rpow ht (by norm_num)
  refine fs_weight_le hN0 ?_
  have h57 : (1 : ℝ) ≤ N ^ (5 / 7 : ℝ) := Real.one_le_rpow hN (by norm_num)
  -- `6πN/t ≤ 38 N^{5/7}` since `N^{2/7} ≤ 2t`
  have h27 : N ≤ 2 * t * N ^ (5 / 7 : ℝ) := by
    have hk : (N ^ (5 / 7 : ℝ)) ^ 14 = N ^ 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    refine fs_le_of_pow_le hN0.le (by positivity) 14 (by norm_num) ?_
    rw [mul_pow, mul_pow, hk]
    have e : (2 : ℝ) ^ 14 * t ^ 14 * N ^ 10 = N ^ 10 * (2 ^ 14 * t ^ 14) := by ring
    rw [e, show N ^ 14 = N ^ 10 * N ^ 4 by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : t ^ 9 ≤ t ^ 14 := pow_le_pow_right₀ ht (by norm_num)
    have h14 : 0 ≤ t ^ 14 := by positivity
    linarith
  have hfirst : 6 * Real.pi * N / t ≤ 38 * N ^ (5 / 7 : ℝ) := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left h27 (by positivity : (0:ℝ) ≤ 6 * Real.pi)
    nlinarith [mul_pos ht0 (lt_of_lt_of_le one_pos h57)]
  have : 40 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) ≥ 40 * N ^ (5 / 7 : ℝ) := by nlinarith
  linarith

theorem fsBlock_second_num {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N) (h35 : t ^ 3 ≤ N ^ 5)
    (hNt : N ≤ t) :
    256 * (N * (16 * (t / (8 * Real.pi * N ^ 2))) ^ (1 / 2 : ℝ)
      + (t / (8 * Real.pi * N ^ 2)) ^ (-(1 / 2 : ℝ))) * N ^ (-(5 / 7 : ℝ))
        ≤ 2560 * t ^ (1 / 14 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  refine fs_weight_le hN0 ?_
  have hk57 : (N ^ (5 / 7 : ℝ)) ^ 14 = N ^ 10 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hkt : (t ^ (1 / 14 : ℝ)) ^ 14 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = t / (8 * Real.pi * N ^ 2) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  -- first term: `N (16λ)^{1/2} ≤ 4 t^{1/14} N^{5/7}`
  have hA : N * (16 * lam) ^ (1 / 2 : ℝ) ≤ 4 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    refine fs_le_of_pow_le (by positivity) (by positivity) 14 (by norm_num) ?_
    have hk : ((16 * lam) ^ (1 / 2 : ℝ)) ^ 14 = (16 * lam) ^ 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have eL : (N * (16 * lam) ^ (1 / 2 : ℝ)) ^ 14 = 4 ^ 14 * (N ^ 14 * lam ^ 7) := by
      rw [mul_pow, hk]; ring
    have eR : (4 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) ^ 14 = 4 ^ 14 * (t * N ^ 10) := by
      rw [mul_pow, mul_pow, hkt, hk57]; ring
    rw [eL, eR]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : N ^ 14 * lam ^ 7 = t * (t ^ 6 / (8 * Real.pi) ^ 7) := by
      rw [hlam]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ ht0.le
    have h6 : t ^ 6 ≤ N ^ 10 := by
      have := pow_le_pow_left₀ (by positivity) h35 2; ring_nf at this ⊢; linarith
    have hp : (1 : ℝ) ≤ (8 * Real.pi) ^ 7 := one_le_pow₀ (by linarith)
    rw [div_le_iff₀ (by positivity)]
    calc t ^ 6 ≤ N ^ 10 := h6
      _ = N ^ 10 * 1 := (mul_one _).symm
      _ ≤ N ^ 10 * (8 * Real.pi) ^ 7 := mul_le_mul_of_nonneg_left hp (by positivity)
  -- second term: `λ^{−1/2} ≤ 6 t^{1/14} N^{5/7}`
  have hB : lam ^ (-(1 / 2 : ℝ)) ≤ 6 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    rw [Real.rpow_neg hlam0.le, ← Real.inv_rpow hlam0.le]
    refine fs_le_of_pow_le (by positivity) (by positivity) 14 (by norm_num) ?_
    have hk : ((lam⁻¹) ^ (1 / 2 : ℝ)) ^ 14 = (lam⁻¹) ^ 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have eR : (6 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) ^ 14 = 6 ^ 14 * (t * N ^ 10) := by
      rw [mul_pow, mul_pow, hkt, hk57]; ring
    rw [hk, eR]
    have e : (lam⁻¹) ^ 7 = (8 * Real.pi) ^ 7 * N ^ 14 / t ^ 7 := by
      rw [hlam]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hN4 : N ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hN0.le hNt 4
    have ht48 : t ^ 4 ≤ t ^ 8 := pow_le_pow_right₀ ht (by norm_num)
    have hp : (8 * Real.pi) ^ 7 ≤ 6 ^ 14 := by
      have : 8 * Real.pi ≤ 32 := by linarith
      calc (8 * Real.pi) ^ 7 ≤ 32 ^ 7 := pow_le_pow_left₀ (by positivity) this 7
        _ ≤ 6 ^ 14 := by norm_num
    have e1 : (8 * Real.pi) ^ 7 * N ^ 14 = ((8 * Real.pi) ^ 7 * N ^ 4) * N ^ 10 := by ring
    have e2 : 6 ^ 14 * (t * N ^ 10) * t ^ 7 = (6 ^ 14 * t ^ 8) * N ^ 10 := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (8 * Real.pi) ^ 7 * N ^ 4 ≤ 6 ^ 14 * t ^ 4 :=
          mul_le_mul hp hN4 (by positivity) (by positivity)
      _ ≤ 6 ^ 14 * t ^ 8 := mul_le_mul_of_nonneg_left ht48 (by positivity)
  calc 256 * (N * (16 * lam) ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2 : ℝ)))
      ≤ 256 * (4 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) + 6 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) := by
        gcongr
    _ = 2560 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by ring

theorem fsBlock_third_num {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N) (h49 : t ^ 4 ≤ N ^ 9)
    (h53 : N ^ 5 ≤ t ^ 3) :
    (128 * N * (t / (8 * Real.pi * N ^ 3)) ^ (1 / 6 : ℝ)
      + 128 * Real.sqrt N / (t / (8 * Real.pi * N ^ 3)) ^ (1 / 6 : ℝ)) * N ^ (-(5 / 7 : ℝ))
        ≤ 384 * t ^ (1 / 14 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  refine fs_weight_le hN0 ?_
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = t / (8 * Real.pi * N ^ 3) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hk57 : (N ^ (5 / 7 : ℝ)) ^ 42 = N ^ 30 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hkt : (t ^ (1 / 14 : ℝ)) ^ 42 = t ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hkl : (lam ^ (1 / 6 : ℝ)) ^ 42 = lam ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]; norm_num
  have hsN : (Real.sqrt N) ^ 42 = N ^ 21 := by
    rw [show (42 : ℕ) = 2 * 21 by norm_num, pow_mul, Real.sq_sqrt hN0.le]
  have hp : (8 * Real.pi) ^ 7 ≤ 2 ^ 42 := by
    have : 8 * Real.pi ≤ 32 := by linarith
    calc (8 * Real.pi) ^ 7 ≤ 32 ^ 7 := pow_le_pow_left₀ (by positivity) this 7
      _ ≤ 2 ^ 42 := by norm_num
  have hp1 : (1 : ℝ) ≤ (8 * Real.pi) ^ 7 := one_le_pow₀ (by linarith)
  -- first term
  have hA : N * lam ^ (1 / 6 : ℝ) ≤ t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    refine fs_le_of_pow_le (by positivity) (by positivity) 42 (by norm_num) ?_
    rw [mul_pow, hkl, mul_pow, hkt, hk57]
    have e : N ^ 42 * lam ^ 7 = N ^ 21 * t ^ 7 / (8 * Real.pi) ^ 7 := by
      rw [hlam]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    calc N ^ 21 * t ^ 7 = (N ^ 21 * t ^ 3) * t ^ 4 := by ring
      _ ≤ (N ^ 21 * t ^ 3) * ((8 * Real.pi) ^ 7 * N ^ 9) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc t ^ 4 ≤ N ^ 9 := h49
            _ ≤ (8 * Real.pi) ^ 7 * N ^ 9 := le_mul_of_one_le_left (by positivity) hp1
      _ = t ^ 3 * N ^ 30 * (8 * Real.pi) ^ 7 := by ring
  -- second term
  have hB : Real.sqrt N / lam ^ (1 / 6 : ℝ) ≤ 2 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    refine fs_le_of_pow_le (by positivity) (by positivity) 42 (by norm_num) ?_
    rw [div_pow, hsN, hkl, mul_pow, mul_pow, hkt, hk57]
    have e : N ^ 21 / lam ^ 7 = (8 * Real.pi) ^ 7 * N ^ 42 / t ^ 7 := by
      rw [hlam]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1210 : N ^ 12 ≤ t ^ 10 := by
      have h60 : (N ^ 12) ^ 5 ≤ (t ^ 10) ^ 5 := by
        calc (N ^ 12) ^ 5 = (N ^ 5) ^ 12 := by ring
          _ ≤ (t ^ 3) ^ 12 := pow_le_pow_left₀ (by positivity) h53 12
          _ = t ^ 36 := by ring
          _ ≤ t ^ 50 := pow_le_pow_right₀ ht (by norm_num)
          _ = (t ^ 10) ^ 5 := by ring
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h60
    calc (8 * Real.pi) ^ 7 * N ^ 42 = ((8 * Real.pi) ^ 7 * N ^ 12) * N ^ 30 := by ring
      _ ≤ (2 ^ 42 * t ^ 10) * N ^ 30 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hp h1210 (by positivity) (by positivity))
            (by positivity)
      _ = 2 ^ 42 * t ^ 3 * N ^ 30 * t ^ 7 := by ring
  calc 128 * N * lam ^ (1 / 6 : ℝ) + 128 * Real.sqrt N / lam ^ (1 / 6 : ℝ)
      = 128 * (N * lam ^ (1 / 6 : ℝ)) + 128 * (Real.sqrt N / lam ^ (1 / 6 : ℝ)) := by ring
    _ ≤ 128 * (t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) + 128 * (2 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) := by
        gcongr
    _ = 384 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by ring

theorem fsBlock_fourth_num {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N) (h94 : N ^ 9 ≤ t ^ 4) :
    224 * (N * (3 * t / (16 * Real.pi * N ^ 4)) ^ (1 / 14 : ℝ)
      + N ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * N ^ 4)) ^ (-(1 / 14 : ℝ)))
        * N ^ (-(5 / 7 : ℝ)) ≤ 672 * t ^ (1 / 14 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  refine fs_weight_le hN0 ?_
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = 3 * t / (16 * Real.pi * N ^ 4) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  -- first term, 14th powers
  have hA : N * lam ^ (1 / 14 : ℝ) ≤ t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    refine fs_le_of_pow_le (by positivity) (by positivity) 14 (by norm_num) ?_
    have hkl : (lam ^ (1 / 14 : ℝ)) ^ 14 = lam := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]; norm_num
    have hkt : (t ^ (1 / 14 : ℝ)) ^ 14 = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    have hk57 : (N ^ (5 / 7 : ℝ)) ^ 14 = N ^ 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [mul_pow, hkl, mul_pow, hkt, hk57]
    have e : N ^ 14 * lam = 3 / (16 * Real.pi) * (t * N ^ 10) := by
      rw [hlam]; field_simp
    rw [e]
    have hc : 3 / (16 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc 3 / (16 * Real.pi) * (t * N ^ 10) ≤ 1 * (t * N ^ 10) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = t * N ^ 10 := one_mul _
  -- second term, 28th powers
  have hB : N ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) ≤ 2 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by
    rw [Real.rpow_neg hlam0.le, ← Real.inv_rpow hlam0.le]
    refine fs_le_of_pow_le (by positivity) (by positivity) 28 (by norm_num) ?_
    have hkl : ((lam⁻¹) ^ (1 / 14 : ℝ)) ^ 28 = (lam⁻¹) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have hkt : (t ^ (1 / 14 : ℝ)) ^ 28 = t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    have hk57 : (N ^ (5 / 7 : ℝ)) ^ 28 = N ^ 20 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have hk34 : (N ^ (3 / 4 : ℝ)) ^ 28 = N ^ 21 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [mul_pow, hk34, hkl, mul_pow, mul_pow, hkt, hk57]
    have e : N ^ 21 * (lam⁻¹) ^ 2 = (16 * Real.pi) ^ 2 * N ^ 29 / (9 * t ^ 2) := by
      rw [hlam]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hp : (16 * Real.pi) ^ 2 ≤ 9 * 2 ^ 28 := by
      have : 16 * Real.pi ≤ 64 := by linarith
      calc (16 * Real.pi) ^ 2 ≤ 64 ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        _ ≤ 9 * 2 ^ 28 := by norm_num
    calc (16 * Real.pi) ^ 2 * N ^ 29 = ((16 * Real.pi) ^ 2 * N ^ 9) * N ^ 20 := by ring
      _ ≤ ((9 * 2 ^ 28) * t ^ 4) * N ^ 20 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hp h94 (by positivity) (by positivity))
            (by positivity)
      _ = 2 ^ 28 * t ^ 2 * N ^ 20 * (9 * t ^ 2) := by ring
  calc 224 * (N * lam ^ (1 / 14 : ℝ) + N ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
      ≤ 224 * (t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) + 2 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ)) := by
        gcongr
    _ = 672 * t ^ (1 / 14 : ℝ) * N ^ (5 / 7 : ℝ) := by ring

/-- **Every dyadic block at `σ = 5/7`.** -/
theorem norm_fsBlock_le {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (hNlow : t ≤ (N : ℝ) ^ 4) (hNup : (N : ℝ) ^ 4 ≤ 10 ^ 4 * t ^ 9) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2560 * t ^ (1 / 14 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ t ^ (1 / 14 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hπ3 := Real.pi_gt_three
  by_cases hkl : 3 * t ≤ 4 * Real.pi * N
  · exact (norm_fsBlock_le_kuzminLandau ht0 hN hkl).trans
      ((fsBlock_kl_num ht hN1 hNup).trans (by linarith))
  · push Not at hkl
    have hNt : (N : ℝ) ≤ t := by nlinarith
    by_cases h35 : t ^ 3 ≤ (N : ℝ) ^ 5
    · have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by
        have h6 : t ^ 3 ≤ ((N : ℝ) ^ 2) ^ 3 :=
          calc t ^ 3 ≤ (N : ℝ) ^ 5 := h35
            _ ≤ (N : ℝ) ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
            _ = ((N : ℝ) ^ 2) ^ 3 := by ring
        have h2 := (pow_le_pow_iff_left₀ ht0.le (by positivity) (by norm_num)).mp h6
        nlinarith [sq_nonneg (N : ℝ)]
      exact (norm_fsBlock_le_second ht0 hN hlam).trans (fsBlock_second_num ht hN1 h35 hNt)
    · push Not at h35
      by_cases h49 : t ^ 4 ≤ (N : ℝ) ^ 9
      · have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3 := by
          have h12 : t ^ 4 ≤ ((N : ℝ) ^ 3) ^ 4 :=
            calc t ^ 4 ≤ (N : ℝ) ^ 9 := h49
              _ ≤ (N : ℝ) ^ 12 := pow_le_pow_right₀ hN1 (by norm_num)
              _ = ((N : ℝ) ^ 3) ^ 4 := by ring
          have h3 := (pow_le_pow_iff_left₀ ht0.le (by positivity) (by norm_num)).mp h12
          nlinarith [pow_pos (lt_of_lt_of_le one_pos hN1) 3]
        exact (norm_fsBlock_le_third_sharp ht0 hN hlam).trans
          ((fsBlock_third_num ht hN1 h49 h35.le).trans (by linarith))
      · push Not at h49
        have hlam : 3 * t ≤ 16 * Real.pi * (N : ℝ) ^ 4 := by
          nlinarith [pow_pos (lt_of_lt_of_le one_pos hN1) 4]
        exact (norm_fsBlock_le_fourth_sharp ht0 hN hlam).trans
          ((fsBlock_fourth_num ht hN1 h49.le).trans (by linarith))

/-- `Nat.log 2 m ≤ log m / log 2`. -/
private theorem natLog_two_le_fs {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2, ← Real.log_rpow (by norm_num)]
  refine Real.log_le_log (by positivity) ?_
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

/-- **`ζ` on the line `Re s = 5/7`.**  `‖ζ(5/7 + it)‖ ≤ 10300 t^{1/14} log t` for `t ≥ 8`. -/
theorem norm_riemannZeta_fiveSevenths_le {t : ℝ} (ht : 8 ≤ t) :
    ‖riemannZeta ((5 / 7 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 10300 * t ^ (1 / 14 : ℝ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlog2 : 2 ≤ Real.log t := by
    have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have : (2 : ℝ) ≤ Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast; linarith
    linarith
  have h15 : (1 : ℝ) ≤ t ^ (1 / 14 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hq : (t ^ (1 / 4 : ℝ)) ^ 4 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  -- the cut points
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈t ^ (1 / 4 : ℝ)⌉₊ + 3 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = Nat.log 2 ⌈t ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  have hc3 : 3 ≤ c := by omega
  have ht14 : (1 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hcR : t ^ (1 / 4 : ℝ) ≤ (c : ℝ) := by
    have := Nat.le_ceil (t ^ (1 / 4 : ℝ)); rw [hc]; push_cast; linarith
  have hcR'' : (c : ℝ) ≤ t ^ (1 / 4 : ℝ) + 4 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ t ^ (1 / 4 : ℝ) by positivity)
    rw [hc]; push_cast; linarith
  have hcR' : (c : ℝ) ≤ 5 * t ^ (1 / 4 : ℝ) := by linarith
  have hc4 : (c : ℝ) ^ 4 ≤ 625 * t := by
    have := pow_le_pow_left₀ (by positivity) hcR' 4
    rw [mul_pow, hq] at this; linarith
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
  have hRlog : (R : ℝ) ≤ 4 * Real.log t := by
    have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hnl := natLog_two_le_fs hceil1
    have hlogc : Real.log (⌈t ^ 2⌉₊ : ℝ) ≤ Real.log 2 + 2 * Real.log t := by
      rw [← Real.log_rpow ht0, ← Real.log_mul (by norm_num) (by positivity)]
      refine Real.log_le_log (by exact_mod_cast hceil1) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; linarith
    have hdiv : Real.log (⌈t ^ 2⌉₊ : ℝ) / Real.log 2 ≤ 1 + 3 * Real.log t := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ Real.log t := by linarith
      nlinarith
    rw [hR]; push_cast; linarith
  -- `(c 2^R)⁴ ≤ 160000 t⁹`
  have hc2R4 : ((c : ℝ) * 2 ^ R) ^ 4 ≤ 160000 * t ^ 9 := by
    have h2R4 : ((2 : ℝ) ^ R) ^ 4 ≤ 256 * t ^ 8 := by
      have := pow_le_pow_left₀ (by positivity) h2R' 4
      calc ((2 : ℝ) ^ R) ^ 4 ≤ (4 * t ^ 2) ^ 4 := this
        _ = 256 * t ^ 8 := by ring
    rw [mul_pow]
    calc (c : ℝ) ^ 4 * ((2 : ℝ) ^ R) ^ 4 ≤ (625 * t) * (256 * t ^ 8) :=
          mul_le_mul hc4 h2R4 (by positivity) (by positivity)
      _ = 160000 * t ^ 9 := by ring
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
  have hK4 : (K : ℝ) ^ 4 ≤ 160000 * t ^ 9 := by
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have : (K : ℝ) ≤ (c : ℝ) * 2 ^ R := by rw [hKR]; linarith
    exact le_trans (pow_le_pow_left₀ hK0 this 4) hc2R4
  -- the blocks
  have hbound : ∀ r < R, ‖∑ n ∈ Finset.Ico (c * 2 ^ r) (c * 2 ^ (r + 1)),
      (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤ 2560 * t ^ (1 / 14 : ℝ) := by
    intro r hr
    have hN1 : 1 ≤ c * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hblk : c * 2 ^ (r + 1) = 2 * (c * 2 ^ r) := by rw [pow_succ]; ring
    rw [hblk]
    have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hc0 : (0 : ℝ) ≤ c := by positivity
    refine norm_fsBlock_le ht1 hN1 ?_ ?_
    · have hcN : (c : ℝ) ≤ ((c * 2 ^ r : ℕ) : ℝ) := by
        push_cast
        exact le_mul_of_one_le_right hc0 h2r
      have := pow_le_pow_left₀ (by positivity) (hcR.trans hcN) 4
      rw [hq] at this; exact this
    · have hr2 : 2 * ((c * 2 ^ r : ℕ) : ℝ) ≤ (c : ℝ) * 2 ^ R := by
        push_cast
        have : (2 : ℝ) ^ r * 2 ≤ 2 ^ R := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      have h16 : (2 * ((c * 2 ^ r : ℕ) : ℝ)) ^ 4 ≤ ((c : ℝ) * 2 ^ R) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hr2 4
      have : (2 * ((c * 2 ^ r : ℕ) : ℝ)) ^ 4 = 16 * ((c * 2 ^ r : ℕ) : ℝ) ^ 4 := by ring
      rw [this] at h16
      linarith
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (5 / 7 : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = 5 / 7 := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  -- head: `≤ 6 t^{1/14}`
  have hhead : 1 + (((c - 1 : ℕ) : ℝ) ^ (1 - 5 / 7 : ℝ) - 1) / (1 - 5 / 7)
      + ((c - 1 : ℕ) : ℝ) ^ (-(5 / 7 : ℝ)) ≤ 6 * t ^ (1 / 14 : ℝ) := by
    have hc1 : (1 : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by
      have : 1 ≤ c - 1 := by omega
      exact_mod_cast this
    have hcle : ((c - 1 : ℕ) : ℝ) ≤ 4 * t ^ (1 / 4 : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have hneg : ((c - 1 : ℕ) : ℝ) ^ (-(5 / 7 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have e : (1 - 5 / 7 : ℝ) = 2 / 7 := by norm_num
    rw [e]
    have h27 : ((c - 1 : ℕ) : ℝ) ^ (2 / 7 : ℝ) ≤ 3 / 2 * t ^ (1 / 14 : ℝ) := by
      refine fs_le_of_pow_le (by positivity) (by positivity) 14 (by norm_num) ?_
      have hk : (((c - 1 : ℕ) : ℝ) ^ (2 / 7 : ℝ)) ^ 14 = ((c - 1 : ℕ) : ℝ) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hkt : (t ^ (1 / 14 : ℝ)) ^ 14 = t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
      rw [hk, mul_pow, hkt]
      have h4 := pow_le_pow_left₀ (by positivity) hcle 4
      rw [mul_pow, hq] at h4
      have h256 : (4 : ℝ) ^ 4 ≤ (3 / 2) ^ 14 := by norm_num
      exact h4.trans (mul_le_mul_of_nonneg_right h256 ht0.le)
    have : (((c - 1 : ℕ) : ℝ) ^ (2 / 7 : ℝ) - 1) / (2 / 7) = 7 / 2 * ((c - 1 : ℕ) : ℝ) ^ (2 / 7 : ℝ) - 7 / 2 := by
      ring
    rw [this]
    linarith
  -- tails
  have htail1 : (K : ℝ) ^ (1 - 5 / 7 : ℝ) / ‖w - 1‖ ≤ 3 := by
    have hnorm : t ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, hwim, Complex.one_im, sub_zero, abs_of_pos ht0] at this
      exact this
    have hpos : 0 < ‖w - 1‖ := lt_of_lt_of_le ht0 hnorm
    rw [div_le_iff₀ hpos]
    have hK27 : (K : ℝ) ^ (1 - 5 / 7 : ℝ) ≤ 3 * t := by
      refine fs_le_of_pow_le (by positivity) (by positivity) 14 (by norm_num) ?_
      have hk : ((K : ℝ) ^ (1 - 5 / 7 : ℝ)) ^ 14 = (K : ℝ) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [hk, mul_pow]
      have h914 : t ^ 9 ≤ t ^ 14 := pow_le_pow_right₀ ht1 (by norm_num)
      have hc : (160000 : ℝ) ≤ 3 ^ 14 := by norm_num
      calc (K : ℝ) ^ 4 ≤ 160000 * t ^ 9 := hK4
        _ ≤ 160000 * t ^ 14 := mul_le_mul_of_nonneg_left h914 (by norm_num)
        _ ≤ 3 ^ 14 * t ^ 14 := mul_le_mul_of_nonneg_right hc (by positivity)
    calc (K : ℝ) ^ (1 - 5 / 7 : ℝ) ≤ 3 * t := hK27
      _ ≤ 3 * ‖w - 1‖ := by linarith only [hnorm]
  have htail2 : ‖w‖ * ((K : ℝ) ^ (-(5 / 7 : ℝ)) / (5 / 7)) ≤ 3 := by
    have hwn : ‖w‖ ≤ 2 * t := by
      rw [hw]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      norm_num; linarith
    have hKn : (K : ℝ) ^ (-(5 / 7 : ℝ)) ≤ t⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      refine inv_anti₀ ht0 ?_
      refine fs_le_of_pow_le ht0.le (by positivity) 7 (by norm_num) ?_
      have hk : ((K : ℝ) ^ (5 / 7 : ℝ)) ^ 7 = (K : ℝ) ^ 5 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [hk]
      calc t ^ 7 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
        _ = (t ^ 2) ^ 5 := by ring
        _ ≤ (K : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hKlow 5
    calc ‖w‖ * ((K : ℝ) ^ (-(5 / 7 : ℝ)) / (5 / 7)) ≤ (2 * t) * (t⁻¹ / (5 / 7)) := by
          gcongr
      _ = 14 / 5 := by field_simp; ring
      _ ≤ 3 := by norm_num
  have htrunc := norm_riemannZeta_le_partialSum (w := w) (by rw [hwre]; norm_num) hw1 hK1
  rw [hwre] at htrunc
  have hsum : ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) : ℂ) ^ (-w)
      = ∑ n ∈ Finset.Ico 1 (c * 2 ^ R), (n : ℂ) ^ (-((5 / 7 : ℝ) : ℂ) - Complex.I * (t : ℂ)) := by
    have hIco : Finset.Ico 1 (c * 2 ^ R) = Finset.Icc 1 K := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_Icc, hK]; omega
    rw [hIco]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hw]; push_cast; ring_nf
  rw [hsum] at htrunc
  have hblocks := norm_dirichlet_sigma_partial_of_blockBound (σ := 5 / 7) (t := t)
    (by norm_num) (by norm_num) hc3 (fun _ => 2560 * t ^ (1 / 14 : ℝ)) (R := R) hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hblocks
  have hR' : (R : ℝ) * (2560 * t ^ (1 / 14 : ℝ)) ≤ 4 * Real.log t * (2560 * t ^ (1 / 14 : ℝ)) :=
    mul_le_mul_of_nonneg_right hRlog (by positivity)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t ^ (1 / 14 : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log t := ⟨_, rfl⟩
  rw [← hu] at hblocks hhead hR' h15 ⊢
  rw [← hL] at hR' hlog2 ⊢
  have hk : u * 2 ≤ u * L := mul_le_mul_of_nonneg_left hlog2 (by linarith)
  have e1 : 4 * L * (2560 * u) = 10240 * (u * L) := by ring
  have e2 : 10300 * u * L = 10300 * (u * L) := by ring
  rw [e1] at hR'
  rw [e2]
  linarith only [htrunc, hblocks, hhead, htail1, htail2, hR', hk, h15]

end

end RHTower
