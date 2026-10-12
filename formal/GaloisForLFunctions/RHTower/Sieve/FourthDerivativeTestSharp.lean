import GaloisForLFunctions.RHTower.Sieve.ThirdDerivativeTestSharp

/-!
# The sharp fourth-derivative test

**Theorem** (`fourth_derivative_test_sharp`).  If the fourth derivative of the phase is pinned
between `λ` and `h·λ` on the span of `N` unit-spaced points, with `0 < λ ≤ 1 ≤ h`, then

  `‖Σ_{n<N} e(G(x₀ + n))‖ ≤ 14·h·(N λ^{1/14} + N^{3/4} λ^{−1/14})`.

This is the order-four case of the sharp `k`-th derivative test, `N λ^{1/(2K−2)} + N^{1−2/K} λ^{−1/(2K−2)}`
with `K = 2^{k−1} = 8`, and it improves the second term `N^{3/4} λ^{−1/8}` of the general test
`kth_derivative_test`.

Proof.  Weyl–van der Corput differencing with window `H`.  The phase differenced by `r < H` has its
third derivative in `[rλ, h·rλ]`, and the sharp third-derivative test (`third_derivative_test_sharp`)
bounds each correlation by `16h(N(rλ)^{1/6} + √N(rλ)^{−1/6})`.  Summing,
`Σ r^{1/6} ≤ H^{7/6}` and `Σ r^{−1/6} ≤ 3H^{5/6}`.  The window `H = ⌈λ^{−1/7}⌉` balances
`N²/H`, `N² λ^{1/6} H^{1/6}` and `N^{3/2} λ^{−1/6} H^{−1/6}` at `N² λ^{1/7} + N^{3/2} λ^{−1/7}`.
For `N ≤ λ^{−1/7}` the trivial bound `N ≤ N^{3/4} λ^{−1/28}` suffices.
-/

namespace RHTower.Sieve

open Real

noncomputable section

theorem sum_Icc_rpow_sixth_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H - 1), (r : ℝ) ^ (1 / 6 : ℝ) ≤ (H : ℝ) * (H : ℝ) ^ (1 / 6 : ℝ) := by
  have hpt : ∀ r ∈ Finset.Icc 1 (H - 1), (r : ℝ) ^ (1 / 6 : ℝ) ≤ (H : ℝ) ^ (1 / 6 : ℝ) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact Real.rpow_le_rpow (Nat.cast_nonneg r) (by exact_mod_cast (le_trans hr.2 (Nat.sub_le H 1)))
      (by norm_num)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 (H - 1)).card : ℝ) ≤ (H : ℝ) := by
    rw [Nat.card_Icc]; exact_mod_cast (Nat.sub_le H 1)
  exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (Nat.cast_nonneg H) _)

theorem sum_Icc_rpow_neg_sixth_le (H : ℕ) (hH : 1 ≤ H) :
    ∑ r ∈ Finset.Icc 1 (H - 1), (r : ℝ) ^ (-(1 / 6 : ℝ)) ≤ 3 * (H : ℝ) ^ (5 / 6 : ℝ) := by
  have hhead := RHTower.sum_rpow_neg_head_le (c := (1 / 6 : ℝ)) (by norm_num) (by norm_num) (H - 1)
  have hsub : (((H - 1 : ℕ) : ℝ)) ^ (1 - (1 / 6 : ℝ)) ≤ (H : ℝ) ^ (5 / 6 : ℝ) := by
    rw [show (1 - (1 / 6 : ℝ)) = 5 / 6 by norm_num]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le H 1) (by norm_num)
  have hone : (1 : ℝ) ≤ (H : ℝ) ^ (5 / 6 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hH) (by norm_num)
  have h56 : (1 - (1 / 6 : ℝ)) = 5 / 6 := by norm_num
  rw [h56] at hhead
  have : (((H - 1 : ℕ) : ℝ)) ^ (5 / 6 : ℝ) / (5 / 6) ≤ (H : ℝ) ^ (5 / 6 : ℝ) / (5 / 6) := by
    rw [h56] at hsub; exact div_le_div_of_nonneg_right hsub (by norm_num)
  linarith

/-- **The window inequality.**  For `1 ≤ H ≤ N` with `(H − 1)λ ≤ 1`,
`H‖Σ‖² ≤ 4N(N + 16h(N λ^{1/6} H·H^{1/6} + √N λ^{−1/6}·3H^{5/6}))`. -/
theorem fourth_derivative_test_window (G : ℕ → ℝ → ℝ) (x₀ : ℝ) (N H : ℕ)
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hgrow1 : 1 ≤ hgrow)
    (hHlam : ((H - 1 : ℕ) : ℝ) * lam ≤ 1)
    (hchain : ∀ i < 4, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (G i) (G (i + 1) x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ G 4 x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), G 4 x ≤ hgrow * lam) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ 4 * (N : ℝ) * ((N : ℝ) + 16 * hgrow * ((N : ℝ) * lam ^ (1 / 6 : ℝ)
          * ((H : ℝ) * (H : ℝ) ^ (1 / 6 : ℝ))
        + Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) * (3 * (H : ℝ) ^ (5 / 6 : ℝ)))) := by
  set a : ℕ → ℂ := fun n =>
    Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) with hadef
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hW := weyl_vdc a hanorm N H hH hHN
  have hlamnn : 0 ≤ lam := hlam0.le
  have hcorr : ∀ r ∈ Finset.Icc 1 (H - 1),
      ‖weylCorr a N r‖ ≤ 16 * hgrow * ((N : ℝ) * lam ^ (1 / 6 : ℝ) * (r : ℝ) ^ (1 / 6 : ℝ)
        + Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) * (r : ℝ) ^ (-(1 / 6 : ℝ))) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1
    have hrN : r < N := by omega
    have hN' : 1 ≤ N - r := by omega
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hlamr0 : 0 < (r : ℝ) * lam := mul_pos hr0 hlam0
    have hlamr1 : (r : ℝ) * lam ≤ 1 := by
      have hrcast : (r : ℝ) ≤ ((H - 1 : ℕ) : ℝ) := by exact_mod_cast hr.2
      exact le_trans (mul_le_mul_of_nonneg_right hrcast hlamnn) hHlam
    have hcast : ((N - r - 1 : ℕ) : ℝ) + (r : ℝ) = ((N - 1 : ℕ) : ℝ) := by
      have hn : (N - r - 1) + r = N - 1 := by omega
      exact_mod_cast hn
    have hspan : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - r - 1 : ℕ) : ℝ)),
        x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) ∧
          x + (r : ℝ) ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) := by
      intro x hx
      constructor <;> constructor <;> linarith [hx.1, hx.2, hcast]
    obtain ⟨Gd, hGddef⟩ : ∃ Gd : ℕ → ℝ → ℝ, Gd = fun i x => G i (x + (r : ℝ)) - G i x := ⟨_, rfl⟩
    have hchain' : ∀ i < 3, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - r - 1 : ℕ) : ℝ)),
        HasDerivAt (Gd i) (Gd (i + 1) x) x := by
      intro i hi x hx
      obtain ⟨hx1, hx2⟩ := hspan x hx
      have hd1 := hchain i (by omega) (x + (r : ℝ)) hx2
      have hd2 := hchain i (by omega) x hx1
      have hs := HasDerivAt.comp_add_const x (r : ℝ) hd1
      rw [hGddef]
      exact hs.sub hd2
    have hslope : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - r - 1 : ℕ) : ℝ)),
        (r : ℝ) * lam ≤ Gd 3 x ∧ Gd 3 x ≤ hgrow * ((r : ℝ) * lam) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hspan x hx
      have hlt : x < x + (r : ℝ) := by linarith
      have hsub : Set.Icc x (x + (r : ℝ)) ⊆ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) :=
        Set.Icc_subset_Icc hx1.1 hx2.2
      have hcont : ContinuousOn (G 3) (Set.Icc x (x + (r : ℝ))) := fun y hy =>
        (hchain 3 (by omega) y (hsub hy)).continuousAt.continuousWithinAt
      have hd : ∀ y ∈ Set.Ioo x (x + (r : ℝ)), HasDerivAt (G 3) (G 4 y) y :=
        fun y hy => hchain 3 (by omega) y (hsub (Set.mem_Icc_of_Ioo hy))
      obtain ⟨ξ, hξ, hval⟩ := exists_hasDerivAt_eq_slope (G 3) (G 4) hlt hcont hd
      have hξspan := hsub (Set.mem_Icc_of_Ioo hξ)
      have hden : (x + (r : ℝ)) - x ≠ 0 := by positivity
      rw [eq_div_iff hden, show (x + (r : ℝ)) - x = (r : ℝ) by ring] at hval
      rw [hGddef]
      constructor
      · calc (r : ℝ) * lam = lam * (r : ℝ) := by ring
          _ ≤ G 4 ξ * (r : ℝ) := mul_le_mul_of_nonneg_right (hlo ξ hξspan) hr0.le
          _ = G 3 (x + (r : ℝ)) - G 3 x := hval
      · calc G 3 (x + (r : ℝ)) - G 3 x = G 4 ξ * (r : ℝ) := hval.symm
          _ ≤ hgrow * lam * (r : ℝ) := mul_le_mul_of_nonneg_right (hhi ξ hξspan) hr0.le
          _ = hgrow * ((r : ℝ) * lam) := by ring
    have htest := third_derivative_test_sharp Gd x₀ (N - r) hN' hlamr0 hlamr1 hgrow1 hchain'
      (fun x hx => (hslope x hx).1) (fun x hx => (hslope x hx).2)
    have hcorrEq : weylCorr a N r = ∑ n ∈ Finset.range (N - r),
        Complex.exp (((2 * Real.pi * Gd 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) := by
      rw [hadef, weylCorr_phase, hGddef]
    rw [hcorrEq]
    have hNr : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N r
    have hsNr : Real.sqrt ((N - r : ℕ) : ℝ) ≤ Real.sqrt N := Real.sqrt_le_sqrt hNr
    have hp1 : ((r : ℝ) * lam) ^ (1 / 6 : ℝ) = lam ^ (1 / 6 : ℝ) * (r : ℝ) ^ (1 / 6 : ℝ) := by
      rw [Real.mul_rpow (Nat.cast_nonneg r) hlamnn]; ring
    have hp2 : ((r : ℝ) * lam) ^ (-(1 / 6 : ℝ))
        = lam ^ (-(1 / 6 : ℝ)) * (r : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [Real.mul_rpow (Nat.cast_nonneg r) hlamnn]; ring
    rw [hp1, hp2] at htest
    refine htest.trans ?_
    have hg : 0 ≤ 16 * hgrow := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hg
    have hA : 0 ≤ lam ^ (1 / 6 : ℝ) * (r : ℝ) ^ (1 / 6 : ℝ) := by positivity
    have hB : 0 ≤ lam ^ (-(1 / 6 : ℝ)) * (r : ℝ) ^ (-(1 / 6 : ℝ)) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hNr hA
    have h2 := mul_le_mul_of_nonneg_right hsNr hB
    nlinarith
  have hsum : ∑ r ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N r‖
      ≤ 16 * hgrow * ((N : ℝ) * lam ^ (1 / 6 : ℝ) * ((H : ℝ) * (H : ℝ) ^ (1 / 6 : ℝ))
        + Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) * (3 * (H : ℝ) ^ (5 / 6 : ℝ))) := by
    refine (Finset.sum_le_sum hcorr).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs1 := sum_Icc_rpow_sixth_le H
    have hs2 := sum_Icc_rpow_neg_sixth_le H hH
    have hf1 : 0 ≤ (N : ℝ) * lam ^ (1 / 6 : ℝ) := by positivity
    have hf2 : 0 ≤ Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hs1 hf1
    have h2 := mul_le_mul_of_nonneg_left hs2 hf2
    have hg : 0 ≤ 16 * hgrow := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hg
  have hfacN : 0 ≤ 4 * (N : ℝ) := by positivity
  have hinside := add_le_add_right hsum (N : ℝ)
  have hscaled := mul_le_mul_of_nonneg_left hinside hfacN
  refine hW.trans (le_trans ?_ hscaled)
  simp only [hadef]
  rw [add_comm (N : ℝ)]

private theorem fourth_combine {A B hg p : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hg1 : 1 ≤ hg)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 9 / 8) :
    4 * A / p ^ 6 + 64 * hg * A * p + 192 * hg * B / p ≤ 192 * hg * (A + B) := by
  have hp0 : 0 < p := by linarith
  have hp6 : 1 ≤ p ^ 6 := one_le_pow₀ hp1
  have t1 : 4 * A / p ^ 6 ≤ 4 * A := div_le_self (by positivity) hp6
  have t1' : 4 * A ≤ 4 * hg * A := by nlinarith [hg1]
  have t2 : 64 * hg * A * p ≤ 72 * hg * A := by
    have h := mul_le_mul_of_nonneg_left hp2 (by positivity : (0:ℝ) ≤ 64 * hg * A)
    linarith
  have t3 : 192 * hg * B / p ≤ 192 * hg * B := div_le_self (by positivity) hp1
  have hgA : 0 ≤ hg * A := by positivity
  linarith

private theorem fourth_square {X Y hg : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hg1 : 1 ≤ hg) :
    192 * hg * (X ^ 2 + Y ^ 2) ≤ (14 * hg * (X + Y)) ^ 2 := by
  have hg2 : hg ≤ hg ^ 2 := by nlinarith [hg1]
  have hXY : 0 ≤ X * Y := mul_nonneg hX hY
  have h1 : 192 * hg * (X ^ 2 + Y ^ 2) ≤ 192 * hg ^ 2 * (X ^ 2 + Y ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : 192 * hg ^ 2 * (X ^ 2 + Y ^ 2) ≤ (14 * hg * (X + Y)) ^ 2 := by
    have : (14 * hg * (X + Y)) ^ 2 = 196 * hg ^ 2 * (X ^ 2 + Y ^ 2) + 392 * hg ^ 2 * (X * Y) := by
      ring
    rw [this]
    have : 0 ≤ hg ^ 2 * (X ^ 2 + Y ^ 2) := by positivity
    have : 0 ≤ hg ^ 2 * (X * Y) := by positivity
    linarith
  exact h1.trans h2

/-- **The sharp fourth-derivative test.** -/
theorem fourth_derivative_test_sharp (G : ℕ → ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hgrow1 : 1 ≤ hgrow)
    (hchain : ∀ i < 4, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (G i) (G (i + 1) x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ G 4 x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), G 4 x ≤ hgrow * lam) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 14 * hgrow * ((N : ℝ) * lam ^ (1 / 14 : ℝ)
        + (N : ℝ) ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ))) := by
  have hlamnn : 0 ≤ lam := hlam0.le
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- base units `u = λ^{1/42}`, `v = N^{1/4}`
  obtain ⟨u, hu⟩ : ∃ u, u = lam ^ (1 / 42 : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (N : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact Real.rpow_le_one hlamnn hlam1 (by norm_num)
  have hv0 : 0 < v := by rw [hv]; positivity
  have hpow : ∀ (x : ℝ) (k : ℕ) (e : ℝ), 0 ≤ x → (x ^ e) ^ k = x ^ (e * k) := by
    intro x k e hx; rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hlamu : lam = u ^ 42 := by
    rw [hu, hpow lam 42 _ hlamnn]; norm_num
  have hNv : (N : ℝ) = v ^ 4 := by rw [hv, hpow _ 4 _ hN0.le]; norm_num
  have hl14 : lam ^ (1 / 14 : ℝ) = u ^ 3 := by
    rw [hu, hpow lam 3 _ hlamnn]; norm_num
  have hl14' : lam ^ (-(1 / 14 : ℝ)) = (u ^ 3)⁻¹ := by
    rw [Real.rpow_neg hlamnn, hl14]
  have hl6 : lam ^ (1 / 6 : ℝ) = u ^ 7 := by rw [hu, hpow lam 7 _ hlamnn]; norm_num
  have hl6' : lam ^ (-(1 / 6 : ℝ)) = (u ^ 7)⁻¹ := by rw [Real.rpow_neg hlamnn, hl6]
  have hN34 : (N : ℝ) ^ (3 / 4 : ℝ) = v ^ 3 := by rw [hv, hpow _ 3 _ hN0.le]; norm_num
  have hsN : Real.sqrt N = v ^ 2 := by
    rw [Real.sqrt_eq_rpow, hv, hpow _ 2 _ hN0.le]; norm_num
  rw [hl14, hl14', hN34, hNv]
  have hg0 : 0 < hgrow := by linarith
  -- short sums: `N ≤ λ^{−1/7} = u^{−6}`
  by_cases hshort : (N : ℝ) ≤ (u ^ 6)⁻¹
  · have htriv := norm_phase_sum_le_card (G 0) x₀ N
    rw [hNv] at htriv hshort
    have h46 : v ^ 4 * u ^ 6 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hshort (by positivity : (0:ℝ) ≤ u ^ 6)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    have hvu3 : v * u ^ 3 ≤ 1 := by
      have h4 : (v * u ^ 3) ^ 4 ≤ 1 := by
        have hu6 : u ^ 6 ≤ 1 := pow_le_one₀ hu0.le hu1
        calc (v * u ^ 3) ^ 4 = (v ^ 4 * u ^ 6) * u ^ 6 := by ring
          _ ≤ 1 * 1 := mul_le_mul h46 hu6 (by positivity) zero_le_one
          _ = 1 := by norm_num
      exact (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).mp h4
    have hv1 : v ≤ (u ^ 3)⁻¹ :=
      calc v = (v * u ^ 3) * (u ^ 3)⁻¹ := by field_simp
        _ ≤ 1 * (u ^ 3)⁻¹ := mul_le_mul_of_nonneg_right hvu3 (by positivity)
        _ = (u ^ 3)⁻¹ := one_mul _
    calc ‖∑ n ∈ Finset.range N,
          Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ≤ v ^ 4 := htriv
      _ = v ^ 3 * v := by ring
      _ ≤ v ^ 3 * (u ^ 3)⁻¹ := mul_le_mul_of_nonneg_left hv1 (by positivity)
      _ ≤ 14 * hgrow * (v ^ 4 * u ^ 3 + v ^ 3 * (u ^ 3)⁻¹) := by
          have : 0 ≤ v ^ 4 * u ^ 3 := by positivity
          have h14 : 1 ≤ 14 * hgrow := by linarith
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ v ^ 3 * (u ^ 3)⁻¹) (by linarith : (0:ℝ) ≤ 14 * hgrow - 1)]
  · -- the window `H = ⌈u^{−6}⌉`
    have hH₀N : (u ^ 6)⁻¹ < (N : ℝ) := lt_of_not_ge hshort
    have hH₀pos : 0 < (u ^ 6)⁻¹ := by positivity
    have hH₀one : 1 ≤ (u ^ 6)⁻¹ := one_le_inv₀ (by positivity) |>.mpr (pow_le_one₀ hu0.le hu1)
    obtain ⟨H, hHdef⟩ : ∃ H : ℕ, H = ⌈(u ^ 6)⁻¹⌉₊ := ⟨_, rfl⟩
    have hH1 : 1 ≤ H := by rw [hHdef]; exact Nat.one_le_ceil_iff.mpr hH₀pos
    have hHN : H ≤ N := by rw [hHdef, Nat.ceil_le]; exact hH₀N.le
    have hH₀H : (u ^ 6)⁻¹ ≤ (H : ℝ) := by rw [hHdef]; exact Nat.le_ceil _
    have hHH₀ : (H : ℝ) < (u ^ 6)⁻¹ + 1 := by rw [hHdef]; exact Nat.ceil_lt_add_one hH₀pos.le
    have hHle : (H : ℝ) ≤ 2 * (u ^ 6)⁻¹ := by linarith
    have hHsub : (((H - 1 : ℕ) : ℝ)) < (u ^ 6)⁻¹ := by
      rw [hHdef]; exact (Nat.lt_ceil).mp (by omega : ⌈(u ^ 6)⁻¹⌉₊ - 1 < ⌈(u ^ 6)⁻¹⌉₊)
    have hHlam : (((H - 1 : ℕ) : ℝ)) * lam ≤ 1 := by
      rw [hlamu]
      have : (u ^ 6)⁻¹ * u ^ 42 ≤ 1 := by
        rw [show (u ^ 6)⁻¹ * u ^ 42 = u ^ 36 by field_simp]
        exact pow_le_one₀ hu0.le hu1
      exact le_trans (mul_le_mul_of_nonneg_right hHsub.le (by positivity)) this
    have hwin := fourth_derivative_test_window G x₀ N H hN hH1 hHN hlam0 hgrow1 hHlam hchain hlo hhi
    -- `w = H^{1/6}` with `u⁻¹ ≤ w ≤ (9/8) u⁻¹`
    obtain ⟨w, hw⟩ : ∃ w, w = (H : ℝ) ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
    have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
    have hw0 : 0 < w := by rw [hw]; positivity
    have hHw : (H : ℝ) = w ^ 6 := by rw [hw, hpow _ 6 _ hH0.le]; norm_num
    have hH56 : (H : ℝ) ^ (5 / 6 : ℝ) = w ^ 5 := by rw [hw, hpow _ 5 _ hH0.le]; norm_num
    have hwlo : u⁻¹ ≤ w := by
      have h6 : (u⁻¹) ^ 6 ≤ w ^ 6 := by rw [← hHw, inv_pow]; exact hH₀H
      exact le_of_pow_le_pow_left₀ (by norm_num) hw0.le h6
    have hwhi : w ≤ 9 / 8 * u⁻¹ := by
      have h6 : w ^ 6 ≤ (9 / 8 * u⁻¹) ^ 6 := by
        rw [← hHw, mul_pow, inv_pow]
        have : (2 : ℝ) ≤ (9 / 8) ^ 6 := by norm_num
        calc (H : ℝ) ≤ 2 * (u ^ 6)⁻¹ := hHle
          _ ≤ (9 / 8) ^ 6 * (u ^ 6)⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h6
    rw [← hw, hH56, hHw, hl6, hl6', hsN, hNv] at hwin
    set S := ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ with hS
    -- `‖Σ‖² ≤ 192 h (v⁸u⁶ + v⁶u^{−6})`
    have hwu : w * u ≤ 9 / 8 := by
      have := mul_le_mul_of_nonneg_right hwhi hu0.le
      rw [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this; exact this
    have hwu1 : 1 ≤ w * u := by
      have := mul_le_mul_of_nonneg_right hwlo hu0.le
      rwa [inv_mul_cancel₀ hu0.ne'] at this
    have hS2 : S ^ 2 ≤ 192 * hgrow * (v ^ 8 * u ^ 6 + v ^ 6 * (u ^ 6)⁻¹) := by
      have hw6 : 0 < w ^ 6 := by positivity
      -- divide the window inequality by `w⁶`
      have hdiv : S ^ 2 ≤ 4 * v ^ 4 * (v ^ 4 + 16 * hgrow * (v ^ 4 * u ^ 7 * (w ^ 6 * w)
          + v ^ 2 * (u ^ 7)⁻¹ * (3 * w ^ 5))) / w ^ 6 := by
        rw [le_div_iff₀ hw6]; linarith
      refine hdiv.trans ?_
      obtain ⟨p, hp⟩ : ∃ p, p = w * u := ⟨_, rfl⟩
      rw [← hp] at hwu hwu1
      have hp0 : 0 < p := by linarith
      have hwp : w = p / u := by rw [hp]; field_simp
      have hid : 4 * v ^ 4 * (v ^ 4 + 16 * hgrow * (v ^ 4 * u ^ 7 * (w ^ 6 * w)
          + v ^ 2 * (u ^ 7)⁻¹ * (3 * w ^ 5))) / w ^ 6
          = 4 * (v ^ 8 * u ^ 6) / p ^ 6 + 64 * hgrow * (v ^ 8 * u ^ 6) * p
            + 192 * hgrow * (v ^ 6 * (u ^ 6)⁻¹) / p := by
        rw [hwp]; field_simp; ring
      rw [hid]
      exact fourth_combine (by positivity) (by positivity) hgrow1 hwu1 hwu
    have hT : S ^ 2 ≤ (14 * hgrow * (v ^ 4 * u ^ 3 + v ^ 3 * (u ^ 3)⁻¹)) ^ 2 := by
      refine hS2.trans ?_
      have hA : v ^ 8 * u ^ 6 = (v ^ 4 * u ^ 3) ^ 2 := by ring
      have hB : v ^ 6 * (u ^ 6)⁻¹ = (v ^ 3 * (u ^ 3)⁻¹) ^ 2 := by rw [mul_pow, inv_pow]; ring
      rw [hA, hB]
      exact fourth_square (by positivity) (by positivity) hgrow1
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hT

end

end RHTower.Sieve
