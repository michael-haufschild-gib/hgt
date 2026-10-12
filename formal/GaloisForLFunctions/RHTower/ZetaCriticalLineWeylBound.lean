import GaloisForLFunctions.RHTower.ZetaCriticalLineFifthPowerBound
import GaloisForLFunctions.RHTower.Sieve.ThirdDerivativeTestSharp

/-!
# Weyl's bound for `ζ` on the critical line

For `t ≥ 8`, `‖ζ(½ + it)‖ ≤ 4000 · t^{1/6} · log t` (`norm_riemannZeta_half_le_sixth`).

Proof.  As for the exponent `1/5` (`norm_riemannZeta_half_le_fifth`): truncate at `M ≥ t²`, take
absolute values below `C = ⌈t^{1/3}⌉ + 3`, and bound the dyadic blocks `[N, 2N)`, `N ≤ 10t^{7/3}`,
of `n^{−½−it}` after partial summation:

* `3t ≤ 4πN`: Kuzmin–Landau, `6π√N/t + 1`;
* `t^{2/3} ≤ N`: the second-derivative test, `256(4√(t/8π)N^{−½} + √(8πN/t))`;
* `t ≤ N³`, `N < t^{2/3}`: the sharp third-derivative test (`third_derivative_test_sharp`) with
  `λ = t/(8πN³)`, `128√N λ^{1/6} + 128λ^{−1/6} = 128(t/8π)^{1/6} + 128(8πN³/t)^{1/6}`.

Each block is at most `1024 t^{1/6}`, the head at most `2 + 4t^{1/6}`, and there are at most
`4 log t` blocks.  The sharp third-derivative term `λ^{−1/6}` (instead of `λ^{−1/4}`) is what moves
the crossing of the second- and third-derivative regimes from `t^{3/5}` to `t^{2/3}` and the exponent
from `1/5` to `1/6`.
-/

namespace RHTower

open RHTower.Sieve Finset Complex

noncomputable section

private theorem rpow_pow_eq_six {x : ℝ} (hx : 0 ≤ x) (p : ℝ) (k : ℕ) :
    (x ^ p) ^ k = x ^ (p * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- **The sharp third-derivative block bound for `∑ n^{−it}`.**  With `λ = t/(8πN³) ≤ 1`, a run of
`L` consecutive Dirichlet phases from `N` inside `[N, 2N]` is at most `128Lλ^{1/6} + 128√L/λ^{1/6}`. -/
theorem dirichlet_block_bound_third_sharp {t : ℝ} (ht : 0 < t) {N L : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1) (hlam1 : t / (8 * Real.pi * (N : ℝ) ^ 3) ≤ 1) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 128 * L * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ)
        + 128 * Real.sqrt L / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) := by
  have hπ := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set lam : ℝ := t / (8 * Real.pi * (N : ℝ) ^ 3) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlo_eq : t / (2 * Real.pi) * (Nat.factorial 2 : ℝ) * ((2 * (N : ℝ)) ^ (2 + 1))⁻¹ = lam := by
    rw [hlamdef]; simp only [Nat.factorial]; push_cast; field_simp; ring
  have hhi_eq : t / (2 * Real.pi) * (Nat.factorial 2 : ℝ) * (((N : ℝ)) ^ (2 + 1))⁻¹ = 8 * lam := by
    rw [hlamdef]; simp only [Nat.factorial]; push_cast; field_simp
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
  have hneg3 : ((-1 : ℝ)) ^ (2 + 1) = -1 := by norm_num
  have hchain : ∀ i < 3, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      HasDerivAt (fun y => -(logPhaseChain t i y)) (-(logPhaseChain t (i + 1) x)) x :=
    fun i _ x hx => (logPhaseChain_hasDerivAt t i (hspan_mem x hx).1).neg
  have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      lam ≤ -(logPhaseChain t 3 x) := by
    intro x hx
    have hb := (logPhaseChain_signed_bounds t ht 2 (lt_of_lt_of_le one_pos hN1)
      (hspan_mem x hx).2).1
    rw [hneg3, neg_one_mul, hlo_eq] at hb
    exact hb
  have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      -(logPhaseChain t 3 x) ≤ 8 * lam := by
    intro x hx
    have hb := (logPhaseChain_signed_bounds t ht 2 (lt_of_lt_of_le one_pos hN1)
      (hspan_mem x hx).2).2
    rw [hneg3, neg_one_mul, hhi_eq] at hb
    exact hb
  have hD := third_derivative_test_sharp (fun i y => -(logPhaseChain t i y)) (N : ℝ) L hL
    hlam0 hlam1 (by norm_num) hchain hlo hhi
  rw [← norm_phase_sum_neg (logPhase t) (N : ℝ) L]
  refine hD.trans (le_of_eq ?_)
  rw [Real.rpow_neg hlam0.le]
  ring

/-- **Sharp third-derivative block**, weighted: for `t ≤ 8πN³`,
`‖∑_{N≤n<2N} n^{−½−it}‖ ≤ (128Nλ^{1/6} + 128√N/λ^{1/6}) N^{−½}`, `λ = t/(8πN³)`. -/
theorem norm_halfBlock_le_third_sharp {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N)
    (hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (128 * N * (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ)
        + 128 * Real.sqrt N / (t / (8 * Real.pi * (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ))
          * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hπ := Real.pi_pos
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

/-- **Sharp third-derivative regime, numerically.**  For `N < t^{2/3}` the block bound is at most
`384 t^{1/6}`. -/
theorem halfBlock_third_sharp_num {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N) (hNt : N < t ^ (2 / 3 : ℝ)) :
    (128 * N * (t / (8 * Real.pi * N ^ 3)) ^ (1 / 6 : ℝ)
      + 128 * Real.sqrt N / (t / (8 * Real.pi * N ^ 3)) ^ (1 / 6 : ℝ)) * N ^ (-(1 / 2 : ℝ))
        ≤ 384 * t ^ (1 / 6 : ℝ) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < t := by linarith
  set lam := t / (8 * Real.pi * N ^ 3) with hlam
  have hlam0 : 0 < lam := by positivity
  have hsN : Real.sqrt N = N ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow N
  have hNN : N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 / 2 : ℝ) := by
    have e : N ^ (1 / 2 : ℝ) = N ^ ((1 : ℝ) + (-(1 / 2))) := by norm_num
    rw [e, Real.rpow_add hN0, Real.rpow_one]
  have hNN' : N ^ (1 / 2 : ℝ) * N ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hN0]; norm_num
  have hsplit : (128 * N * lam ^ (1 / 6 : ℝ) + 128 * Real.sqrt N / lam ^ (1 / 6 : ℝ))
      * N ^ (-(1 / 2 : ℝ))
      = 128 * (N ^ (1 / 2 : ℝ) * lam ^ (1 / 6 : ℝ)) + 128 / lam ^ (1 / 6 : ℝ) := by
    rw [hsN]
    have hl : 0 < lam ^ (1 / 6 : ℝ) := by positivity
    field_simp
    linear_combination ((lam ^ (1 / 6 : ℝ)) ^ 2) * hNN + hNN'
  rw [hsplit]
  have h1 : (1 : ℝ) ≤ t ^ (1 / 6 : ℝ) := Real.one_le_rpow ht (by norm_num)
  -- `√N λ^{1/6} = (t/8π)^{1/6} ≤ t^{1/6}`
  have hT1 : N ^ (1 / 2 : ℝ) * lam ^ (1 / 6 : ℝ) ≤ t ^ (1 / 6 : ℝ) := by
    have ha : 0 ≤ N ^ (1 / 2 : ℝ) * lam ^ (1 / 6 : ℝ) := by positivity
    rw [← pow_le_pow_iff_left₀ ha (by positivity) (by norm_num : (6 : ℕ) ≠ 0), mul_pow,
      rpow_pow_eq_six hN0.le, rpow_pow_eq_six hlam0.le, rpow_pow_eq_six ht0.le]
    norm_num
    rw [hlam]
    have e : N ^ 3 * (t / (8 * Real.pi * N ^ 3)) = t / (8 * Real.pi) := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  -- `λ^{−1/6} = (8πN³/t)^{1/6} ≤ 2 t^{1/6}`
  have hT2 : 128 / lam ^ (1 / 6 : ℝ) ≤ 256 * t ^ (1 / 6 : ℝ) := by
    have hl : 0 < lam ^ (1 / 6 : ℝ) := by positivity
    rw [div_le_iff₀ hl]
    have hb : 1 ≤ 2 * (t ^ (1 / 6 : ℝ) * lam ^ (1 / 6 : ℝ)) := by
      have ha : 0 ≤ t ^ (1 / 6 : ℝ) * lam ^ (1 / 6 : ℝ) := by positivity
      have hk : (1 / 2 : ℝ) ≤ t ^ (1 / 6 : ℝ) * lam ^ (1 / 6 : ℝ) := by
        rw [← pow_le_pow_iff_left₀ (by norm_num) ha (by norm_num : (6 : ℕ) ≠ 0), mul_pow,
          rpow_pow_eq_six ht0.le, rpow_pow_eq_six hlam0.le]
        norm_num
        rw [hlam]
        have hN3 : N ^ 3 < t ^ 2 := by
          have h := pow_lt_pow_left₀ hNt hN0.le (by norm_num : (3 : ℕ) ≠ 0)
          rw [rpow_pow_eq_six ht0.le] at h
          norm_num at h
          exact h
        rw [show t * (t / (8 * Real.pi * N ^ 3)) = t ^ 2 / (8 * Real.pi * N ^ 3) by ring,
          le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    nlinarith
  linarith

/-- **Second-derivative regime, numerically**, at the threshold `t^{2/3}`: for `t^{2/3} ≤ N` and
`4πN < 3t` the block bound is at most `1024 t^{1/6}`. -/
theorem halfBlock_second_num_sixth {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N)
    (hNt : t ^ (2 / 3 : ℝ) ≤ N) (hNkl : 4 * Real.pi * N < 3 * t) :
    256 * (N * (16 * (t / (8 * Real.pi * N ^ 2))) ^ (1 / 2 : ℝ)
      + (t / (8 * Real.pi * N ^ 2)) ^ (-(1 / 2 : ℝ))) * N ^ (-(1 / 2 : ℝ))
        ≤ 1024 * t ^ (1 / 6 : ℝ) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < t := by linarith
  set lam := t / (8 * Real.pi * N ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  have hT1 : N * (16 * lam) ^ (1 / 2 : ℝ) * N ^ (-(1 / 2 : ℝ)) ≤ t ^ (1 / 6 : ℝ) := by
    have ha : 0 ≤ N * (16 * lam) ^ (1 / 2 : ℝ) * N ^ (-(1 / 2 : ℝ)) := by positivity
    rw [← pow_le_pow_iff_left₀ ha (by positivity) (two_ne_zero)]
    rw [mul_pow, mul_pow, rpow_pow_eq_six (by positivity), rpow_pow_eq_six hN0.le,
      rpow_pow_eq_six ht0.le]
    norm_num
    rw [Real.rpow_neg_one]
    have h23 : t ^ (2 / 3 : ℝ) * t ^ (1 / 3 : ℝ) = t := by
      rw [← Real.rpow_add ht0]; norm_num
    have h13 : t / N ≤ t ^ (1 / 3 : ℝ) := by
      rw [div_le_iff₀ hN0]
      calc t = t ^ (2 / 3 : ℝ) * t ^ (1 / 3 : ℝ) := h23.symm
        _ ≤ N * t ^ (1 / 3 : ℝ) := by gcongr
        _ = t ^ (1 / 3 : ℝ) * N := by ring
    calc N ^ 2 * (16 * lam) * N⁻¹ = 2 / Real.pi * (t / N) := by
          rw [hlam]; field_simp; ring
      _ ≤ 1 * (t / N) := by
          gcongr
          rw [div_le_one hπ]; linarith
      _ ≤ t ^ (1 / 3 : ℝ) := by rw [one_mul]; exact h13
  have hT2 : lam ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) ≤ 3 * t ^ (1 / 6 : ℝ) := by
    have h1 : (1 : ℝ) ≤ t ^ (1 / 6 : ℝ) := Real.one_le_rpow ht (by norm_num)
    have ha : 0 ≤ lam ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) := by positivity
    have hb : lam ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) ≤ 3 := by
      rw [← pow_le_pow_iff_left₀ ha (by norm_num) (two_ne_zero)]
      rw [mul_pow, rpow_pow_eq_six hlam0.le, rpow_pow_eq_six hN0.le]
      norm_num
      rw [Real.rpow_neg_one, Real.rpow_neg_one, hlam]
      have : (t / (8 * Real.pi * N ^ 2))⁻¹ * N⁻¹ = 8 * Real.pi * N / t := by
        field_simp
      rw [this, div_le_iff₀ ht0]
      nlinarith
    linarith
  have e : 256 * (N * (16 * lam) ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2 : ℝ))) * N ^ (-(1 / 2 : ℝ))
      = 256 * (N * (16 * lam) ^ (1 / 2 : ℝ) * N ^ (-(1 / 2 : ℝ))
        + lam ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ))) := by ring
  rw [e]
  linarith

/-- **Kuzmin–Landau regime, numerically**, exponent `1/6`. -/
theorem halfBlock_kl_num_sixth {t N : ℝ} (ht : 1 ≤ t) (hN : 1 ≤ N)
    (hNup : N ≤ 10 * t ^ (7 / 3 : ℝ)) :
    (6 * Real.pi * N / t + 1) * N ^ (-(1 / 2 : ℝ)) ≤ 100 * t ^ (1 / 6 : ℝ) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hN0 : 0 < N := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : (1 : ℝ) ≤ t ^ (1 / 6 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hNh : N ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hsplit : (6 * Real.pi * N / t + 1) * N ^ (-(1 / 2 : ℝ))
      = 6 * Real.pi * (N * N ^ (-(1 / 2 : ℝ))) / t + N ^ (-(1 / 2 : ℝ)) := by ring
  have hNN : N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 / 2 : ℝ) := by
    have e : N ^ (1 / 2 : ℝ) = N ^ ((1 : ℝ) + (-(1 / 2))) := by norm_num
    rw [e, Real.rpow_add hN0, Real.rpow_one]
  rw [hsplit, hNN]
  have hsq : N ^ (1 / 2 : ℝ) ≤ 4 * t ^ (7 / 6 : ℝ) := by
    have ha : 0 ≤ N ^ (1 / 2 : ℝ) := by positivity
    rw [← pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero, mul_pow, rpow_pow_eq_six hN0.le,
      rpow_pow_eq_six ht0.le]
    norm_num
    linarith
  have h76 : t ^ (7 / 6 : ℝ) / t = t ^ (1 / 6 : ℝ) := by
    rw [div_eq_iff ht0.ne', ← Real.rpow_add_one ht0.ne']; norm_num
  have hmain : 6 * Real.pi * N ^ (1 / 2 : ℝ) / t ≤ 96 * t ^ (1 / 6 : ℝ) := by
    calc 6 * Real.pi * N ^ (1 / 2 : ℝ) / t ≤ 6 * Real.pi * (4 * t ^ (7 / 6 : ℝ)) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) ht0.le
      _ = 24 * Real.pi * (t ^ (7 / 6 : ℝ) / t) := by ring
      _ = 24 * Real.pi * t ^ (1 / 6 : ℝ) := by rw [h76]
      _ ≤ 96 * t ^ (1 / 6 : ℝ) := by nlinarith
  linarith

/-- **Every dyadic block, exponent `1/6`.** -/
theorem norm_halfBlock_le_sixth {t : ℝ} (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (hNlow : t ≤ (N : ℝ) ^ 3) (hNup : (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ)) :
    ‖∑ n ∈ Finset.Ico N (2 * N), (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 1024 * t ^ (1 / 6 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ t ^ (1 / 6 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hπ3 := Real.pi_gt_three
  by_cases hkl : 3 * t ≤ 4 * Real.pi * N
  · exact (norm_halfBlock_le_kuzminLandau ht0 hN hkl).trans
      ((halfBlock_kl_num_sixth ht hN1 hNup).trans (by nlinarith))
  · push Not at hkl
    by_cases h23 : t ^ (2 / 3 : ℝ) ≤ N
    · have hsq : t ^ (4 / 3 : ℝ) ≤ (N : ℝ) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) h23 2
        rw [rpow_pow_eq_six ht0.le] at h
        norm_num at h
        exact h
      have h43 : t ≤ t ^ (4 / 3 : ℝ) := by
        calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
          _ ≤ t ^ (4 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
      have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by nlinarith
      exact (norm_halfBlock_le_second ht0 hN hlam).trans (halfBlock_second_num_sixth ht hN1 h23 hkl)
    · push Not at h23
      have hlam : t ≤ 8 * Real.pi * (N : ℝ) ^ 3 := by nlinarith
      exact (norm_halfBlock_le_third_sharp ht0 hN hlam).trans
        ((halfBlock_third_sharp_num ht hN1 h23).trans (by nlinarith))

/-- `Nat.log 2 m ≤ log m / log 2`. -/
private theorem natLog_two_le_six {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2, ← Real.log_rpow (by norm_num)]
  refine Real.log_le_log (by positivity) ?_
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

/-- **Weyl's bound.**  `‖ζ(½ + it)‖ ≤ 4200 t^{1/6} log t` for `t ≥ 8`. -/
theorem norm_riemannZeta_half_le_sixth {t : ℝ} (ht : 8 ≤ t) :
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 4200 * t ^ (1 / 6 : ℝ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlog2 : 2 ≤ Real.log t := by
    have h8 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have : (2 : ℝ) ≤ Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast; linarith
    linarith
  have h15 : (1 : ℝ) ≤ t ^ (1 / 6 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  -- the cut points
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈t ^ (1 / 3 : ℝ)⌉₊ + 3 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = Nat.log 2 ⌈t ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  have hc3 : 3 ≤ c := by omega
  have ht13 : (1 : ℝ) ≤ t ^ (1 / 3 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hcR : t ^ (1 / 3 : ℝ) ≤ (c : ℝ) := by
    have := Nat.le_ceil (t ^ (1 / 3 : ℝ)); rw [hc]; push_cast; linarith
  have hcR'' : (c : ℝ) ≤ t ^ (1 / 3 : ℝ) + 4 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ t ^ (1 / 3 : ℝ) by positivity)
    rw [hc]; push_cast; linarith
  have hcR' : (c : ℝ) ≤ 5 * t ^ (1 / 3 : ℝ) := by linarith
  have hceil2 : (⌈t ^ 2⌉₊ : ℝ) ≤ 2 * t ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ t ^ 2 by positivity); nlinarith
  have hceil1 : 1 ≤ ⌈t ^ 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have h2R : t ^ 2 < (2 : ℝ) ^ R := by
    have h1 : ⌈t ^ 2⌉₊ < 2 ^ R := by
      rw [hR]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : t ^ 2 ≤ (⌈t ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈t ^ 2⌉₊ : ℝ) < ((2 ^ R : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3; linarith
  have h2R' : (2 : ℝ) ^ R ≤ 4 * t ^ 2 := by
    rw [hR, pow_succ]
    have h1 := Nat.pow_log_le_self 2 (show ⌈t ^ 2⌉₊ ≠ 0 by omega)
    have h3 : ((2 ^ Nat.log 2 ⌈t ^ 2⌉₊ : ℕ) : ℝ) ≤ (⌈t ^ 2⌉₊ : ℝ) := by exact_mod_cast h1
    push_cast at h3; linarith
  have hRlog : (R : ℝ) ≤ 4 * Real.log t := by
    have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hnl := natLog_two_le_six hceil1
    have hlogc : Real.log (⌈t ^ 2⌉₊ : ℝ) ≤ Real.log 2 + 2 * Real.log t := by
      rw [← Real.log_rpow ht0, ← Real.log_mul (by norm_num) (by positivity)]
      refine Real.log_le_log (by exact_mod_cast hceil1) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; linarith
    have hdiv : Real.log (⌈t ^ 2⌉₊ : ℝ) / Real.log 2 ≤ 1 + 3 * Real.log t := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ Real.log t := by linarith
      nlinarith
    rw [hR]; push_cast; linarith
  -- truncation point
  have hc2R : (c : ℝ) * 2 ^ R ≤ 20 * t ^ (7 / 3 : ℝ) := by
    have h73 : t ^ (1 / 3 : ℝ) * t ^ 2 = t ^ (7 / 3 : ℝ) := by
      rw [show (7 / 3 : ℝ) = 1 / 3 + 2 by norm_num, Real.rpow_add ht0]; norm_num
    have := mul_le_mul hcR' h2R' (by positivity) (by positivity)
    nlinarith
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
  have hKup : (K : ℝ) ≤ 20 * t ^ (7 / 3 : ℝ) := by rw [hKR]; linarith
  -- the Dirichlet sum
  have hbound : ∀ r < R, ‖∑ n ∈ Finset.Ico (c * 2 ^ r) (c * 2 ^ (r + 1)),
      (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤ 1024 * t ^ (1 / 6 : ℝ) := by
    intro r hr
    have hN1 : 1 ≤ c * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hblk : c * 2 ^ (r + 1) = 2 * (c * 2 ^ r) := by rw [pow_succ]; ring
    rw [hblk]
    have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hc0 : (0 : ℝ) ≤ c := by positivity
    refine norm_halfBlock_le_sixth ht1 hN1 ?_ ?_
    · have hcN : (c : ℝ) ≤ ((c * 2 ^ r : ℕ) : ℝ) := by
        push_cast
        exact le_mul_of_one_le_right hc0 h2r
      have h3 : (t ^ (1 / 3 : ℝ)) ^ 3 = t := by
        rw [rpow_pow_eq_six ht0.le]; norm_num
      have := pow_le_pow_left₀ (by positivity) (hcR.trans hcN) 3
      rw [h3] at this; exact this
    · have hr2 : ((c * 2 ^ r : ℕ) : ℝ) ≤ (c : ℝ) * 2 ^ R / 2 := by
        push_cast
        have : (2 : ℝ) ^ r * 2 ≤ 2 ^ R := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        rw [le_div_iff₀ (by norm_num), mul_assoc]
        exact mul_le_mul_of_nonneg_left this hc0
      linarith only [hr2, hc2R]
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = 1 / 2 := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  -- head
  have hhead : 1 + (((c - 1 : ℕ) : ℝ) ^ (1 - 1 / 2 : ℝ) - 1) / (1 - 1 / 2)
      + ((c - 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 6 * t ^ (1 / 6 : ℝ) := by
    have hc1 : (1 : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by
      have : 1 ≤ c - 1 := by omega
      exact_mod_cast this
    have hcle : ((c - 1 : ℕ) : ℝ) ≤ 4 * t ^ (1 / 3 : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have hneg : ((c - 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hsq : ((c - 1 : ℕ) : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ 2 * t ^ (1 / 6 : ℝ) := by
      have ha : 0 ≤ ((c - 1 : ℕ) : ℝ) ^ (1 - 1 / 2 : ℝ) := by positivity
      rw [← pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero, mul_pow,
        rpow_pow_eq_six (by positivity), rpow_pow_eq_six ht0.le]
      norm_num
      linarith
    have e : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [e] at hsq ⊢
    have : (((c - 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) - 1) / (1 / 2) = 2 * ((c - 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) - 2 := by
      ring
    rw [this]
    linarith only [hsq, hneg, h15]
  -- tails
  have htail1 : (K : ℝ) ^ (1 - 1 / 2 : ℝ) / ‖w - 1‖ ≤ 5 * t ^ (1 / 6 : ℝ) := by
    have hnorm : t ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, hwim, Complex.one_im, sub_zero, abs_of_pos ht0] at this
      exact this
    rw [div_le_iff₀ (by linarith)]
    have hsqK : (K : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ 5 * t ^ (7 / 6 : ℝ) := by
      have ha : 0 ≤ (K : ℝ) ^ (1 - 1 / 2 : ℝ) := by positivity
      rw [← pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero, mul_pow,
        rpow_pow_eq_six (by positivity), rpow_pow_eq_six ht0.le]
      norm_num
      linarith
    have h76 : t ^ (7 / 6 : ℝ) ≤ t ^ (1 / 6 : ℝ) * t := by
      calc t ^ (7 / 6 : ℝ) = t ^ (1 / 6 : ℝ) * t := by
            rw [← Real.rpow_add_one ht0.ne']; norm_num
        _ ≤ t ^ (1 / 6 : ℝ) * t :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)) ht0.le
    calc (K : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ 5 * t ^ (7 / 6 : ℝ) := hsqK
      _ ≤ 5 * (t ^ (1 / 6 : ℝ) * t) := by linarith
      _ ≤ 5 * t ^ (1 / 6 : ℝ) * ‖w - 1‖ := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hnorm (by positivity)
  have htail2 : ‖w‖ * ((K : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) ≤ 4 := by
    have hwn : ‖w‖ ≤ 2 * t := by
      rw [hw]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      norm_num; linarith
    have hKn : (K : ℝ) ^ (-(1 / 2 : ℝ)) ≤ t⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      refine inv_anti₀ ht0 ?_
      have ha : 0 ≤ (K : ℝ) ^ (1 / 2 : ℝ) := by positivity
      rw [← pow_le_pow_iff_left₀ ht0.le ha two_ne_zero, rpow_pow_eq_six (by positivity)]
      norm_num; exact hKlow
    calc ‖w‖ * ((K : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) ≤ (2 * t) * (t⁻¹ / (1 / 2)) := by
          gcongr
      _ = 4 := by field_simp; ring
  have htrunc := norm_riemannZeta_le_partialSum (w := w) (by rw [hwre]; norm_num) hw1 hK1
  rw [hwre] at htrunc
  have hsum : ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) : ℂ) ^ (-w)
      = ∑ n ∈ Finset.Ico 1 (c * 2 ^ R), (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ)) := by
    have hIco : Finset.Ico 1 (c * 2 ^ R) = Finset.Icc 1 K := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_Icc, hK]; omega
    rw [hIco]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hw]; push_cast; ring_nf
  rw [hsum] at htrunc
  -- blocks
  have hblocks := norm_dirichlet_sigma_partial_of_blockBound (σ := 1 / 2) (t := t)
    (by norm_num) (by norm_num) hc3 (fun _ => 1024 * t ^ (1 / 6 : ℝ)) (R := R) hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hblocks
  have hR' : (R : ℝ) * (1024 * t ^ (1 / 6 : ℝ)) ≤ 4 * Real.log t * (1024 * t ^ (1 / 6 : ℝ)) :=
    mul_le_mul_of_nonneg_right hRlog (by positivity)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log t := ⟨_, rfl⟩
  rw [← hu] at hblocks hhead htail1 hR' h15 ⊢
  rw [← hL] at hR' hlog2 ⊢
  have hk : u * 2 ≤ u * L := mul_le_mul_of_nonneg_left hlog2 (by linarith)
  have e1 : 4 * L * (1024 * u) = 4096 * (u * L) := by ring
  have e2 : 4200 * u * L = 4200 * (u * L) := by ring
  rw [e1] at hR'
  rw [e2]
  linarith only [htrunc, hblocks, hhead, htail1, htail2, hR', hk, h15]

end

end RHTower
