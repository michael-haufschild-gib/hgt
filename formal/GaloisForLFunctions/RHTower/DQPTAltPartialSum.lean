import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# DQPT: the alternating Dirichlet partial sum and its paired tail

This is the first module of the formalisation of

> ShiJie Wei, Yue Zhai, Quanfeng Lu, Wentao Yang, Pan Gao, Chao Wei, Junda Song, Franco Nori,
> Tao Xin, GuiLu Long, *The Riemann Hypothesis Emerges in Dynamical Quantum Phase Transitions*,
> arXiv:2511.11199; Nature Communications, DOI `10.1038/s41467-026-74935-8`.

Supplementary Note 1 of that paper studies

`S_N(s) = ∑_{n=1}^N (−1)^{n+1} n^{−s}`,  `R_N(s) = ∑_{n>N} (−1)^{n+1} n^{−s}`.

The tail `R_N` is only conditionally convergent, so we work with its **paired** form

`A_N(s) = ∑_{j≥0} ((N+1+2j)^{−s} − (N+2+2j)^{−s})`,

which converges absolutely on `{Re s > 0}` and satisfies `R_N(s) = (−1)^N A_N(s)`.

Main results:
* `dqptRp_sub_norm_le` — the mean-value bound `‖a^{−s} − b^{−s}‖ ≤ ‖s‖·a^{−β−1}(b−a)`;
* `dqptRp_second_diff_norm_le` — the second-difference bound
  `‖a^{−s} − 2(a+1)^{−s} + (a+2)^{−s}‖ ≤ ‖s‖·‖s+1‖·a^{−β−2}`;
* `dqptAltTail_add_succ` — the telescoping law `A_N + A_{N+1} = (N+1)^{−s}`;
* `dqptEta_eq_altPartialSum_add_tail` — **`(1 − 2^{1−s})·ζ(s) = S_N(s) + (−1)^N A_N(s)`**,
  the exact finite-`N` decomposition behind Supplementary Note 1.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The real-base power `x ↦ x^{−s}` -/

/-- The real-base power `x ↦ x^{−s}` used throughout the DQPT modules. -/
def dqptRp (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-s)

theorem dqptRp_norm {s : ℂ} {x : ℝ} (hx : 0 < x) : ‖dqptRp s x‖ = x ^ (-s.re) := by
  rw [dqptRp, norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]

theorem hasDerivAt_dqptRp {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => dqptRp s y) ((-s) * dqptRp (s + 1) x) x := by
  have hsne : (-s) ≠ 0 := by
    intro h; exact (ne_of_gt hs) (by rw [neg_eq_zero] at h; rw [h]; simp)
  have h := hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hsne
  refine h.congr_deriv ?_
  rw [dqptRp]
  congr 2
  ring

/-- **Mean-value bound.**  On `[a, b] ⊆ (0, ∞)` the map `x ↦ x^{−s}` has derivative of norm at
most `‖s‖·a^{−Re s−1}`. -/
theorem dqptRp_sub_norm_le {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖dqptRp s a - dqptRp s b‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  set C : ℝ := ‖s‖ * a ^ (-s.re - 1) with hC
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun y : ℝ => dqptRp s y) ((-s) * dqptRp (s + 1) x) (Icc a b) x := by
    intro x hx
    exact (hasDerivAt_dqptRp hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖(-s) * dqptRp (s + 1) x‖ ≤ C := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    rw [norm_mul, norm_neg, hC, dqptRp_norm hx0]
    have hre : -(s + 1).re = -s.re - 1 := by
      rw [Complex.add_re, Complex.one_re]; ring
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg s)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (right_mem_Icc.2 hab)
  rw [norm_sub_rev]
  exact key

/-- **Second-difference bound.**  Applying the mean-value bound twice — once to `x ↦ x^{−s}` and
once to `x ↦ x^{−(s+1)}` — gives `‖a^{−s} − 2(a+1)^{−s} + (a+2)^{−s}‖ ≤ ‖s‖·‖s+1‖·a^{−β−2}`. -/
theorem dqptRp_second_diff_norm_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖dqptRp s a - 2 * dqptRp s (a + 1) + dqptRp s (a + 2)‖
      ≤ ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) := by
  set ψ : ℝ → ℂ := fun y => dqptRp s y - dqptRp s (y + 1) with hψ
  set C : ℝ := ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) with hC
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hderiv : ∀ x ∈ Icc a (a + 1),
      HasDerivWithinAt ψ ((-s) * dqptRp (s + 1) x - (-s) * dqptRp (s + 1) (x + 1))
        (Icc a (a + 1)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have h1 : HasDerivAt (fun y : ℝ => dqptRp s y) ((-s) * dqptRp (s + 1) x) x :=
      hasDerivAt_dqptRp hs hx0
    have h2 : HasDerivAt (fun y : ℝ => dqptRp s (y + 1)) ((-s) * dqptRp (s + 1) (x + 1)) x := by
      have hx1 : (0 : ℝ) < x + 1 := by linarith
      exact HasDerivAt.comp_add_const x 1 (hasDerivAt_dqptRp hs hx1)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a (a + 1),
      ‖(-s) * dqptRp (s + 1) x - (-s) * dqptRp (s + 1) (x + 1)‖ ≤ C := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hstep := dqptRp_sub_norm_le hs1 hx0 (by linarith : x ≤ x + 1)
    have hre : -(s + 1).re - 1 = -s.re - 2 := by
      rw [Complex.add_re, Complex.one_re]; ring
    rw [hre] at hstep
    have hsimp : x + 1 - x = 1 := by ring
    rw [hsimp, mul_one] at hstep
    have hfact : (-s) * dqptRp (s + 1) x - (-s) * dqptRp (s + 1) (x + 1)
        = (-s) * (dqptRp (s + 1) x - dqptRp (s + 1) (x + 1)) := by ring
    rw [hfact, norm_mul, norm_neg, hC]
    have hmono : x ^ (-s.re - 2) ≤ a ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
    calc ‖s‖ * ‖dqptRp (s + 1) x - dqptRp (s + 1) (x + 1)‖
        ≤ ‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg s)
      _ ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
          exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
      _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
    (right_mem_Icc.2 (by linarith))
  have hsimp : a + 1 - a = 1 := by ring
  rw [hsimp, mul_one] at key
  have hrw : ψ (a + 1) - ψ a = -(dqptRp s a - 2 * dqptRp s (a + 1) + dqptRp s (a + 2)) := by
    rw [hψ]
    simp only
    have h2 : a + 1 + 1 = a + 2 := by ring
    rw [h2]
    ring
  rw [hrw, norm_neg] at key
  exact key

/-! ## The partial sum and the paired tail -/

/-- `S_N(s) = ∑_{n=1}^N (−1)^{n+1} n^{−s}`, the `N`-term partial sum of the alternating
Dirichlet series (Supplementary Note 1, equation (1.1)). -/
def dqptAltPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * dqptRp s ((n : ℝ) + 1)

@[simp] theorem dqptAltPartialSum_zero (s : ℂ) : dqptAltPartialSum s 0 = 0 := by
  simp [dqptAltPartialSum]

theorem dqptAltPartialSum_succ (s : ℂ) (N : ℕ) :
    dqptAltPartialSum s (N + 1) = dqptAltPartialSum s N + (-1 : ℂ) ^ N * dqptRp s ((N : ℝ) + 1) := by
  rw [dqptAltPartialSum, dqptAltPartialSum, Finset.sum_range_succ]

/-- The `j`-th paired tail term `(N+1+2j)^{−s} − (N+2+2j)^{−s}`. -/
def dqptAltTailTerm (s : ℂ) (N : ℕ) (j : ℕ) : ℂ :=
  dqptRp s ((N : ℝ) + 1 + 2 * j) - dqptRp s ((N : ℝ) + 2 + 2 * j)

/-- `A_N(s) = ∑_{j≥0} ((N+1+2j)^{−s} − (N+2+2j)^{−s})`: the paired tail. -/
def dqptAltTail (s : ℂ) (N : ℕ) : ℂ := ∑' j : ℕ, dqptAltTailTerm s N j

theorem norm_dqptAltTailTerm_le {s : ℂ} (hs : 0 < s.re) (N j : ℕ) :
    ‖dqptAltTailTerm s N j‖ ≤ ‖s‖ * ((N : ℝ) + 1 + 2 * j) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 + 2 * j := by positivity
  have hab : (N : ℝ) + 1 + 2 * j ≤ (N : ℝ) + 2 + 2 * j := by linarith
  have h := dqptRp_sub_norm_le hs ha hab
  have hlen : (N : ℝ) + 2 + 2 * j - ((N : ℝ) + 1 + 2 * j) = 1 := by ring
  rw [hlen, mul_one] at h
  exact h

theorem summable_dqptAltTailTerm {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (dqptAltTailTerm s N) := by
  have hg : Summable (fun j : ℕ => ‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1)) := by
    apply Summable.mul_left
    have h2 := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -s.re - 1 < -1 by linarith))
    refine h2.congr (fun n => ?_)
    push_cast; ring_nf
  refine Summable.of_norm_bounded hg (fun j => ?_)
  refine (norm_dqptAltTailTerm_le hs N j).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- At `N = 0` the paired tail is the corpus's paired eta series. -/
theorem dqptAltTail_zero (s : ℂ) : dqptAltTail s 0 = etaPair s := by
  rw [dqptAltTail, etaPair]
  refine tsum_congr (fun j => ?_)
  rw [dqptAltTailTerm, etaTerm, dqptRp, dqptRp]
  have e1 : ((0 : ℕ) : ℝ) + 1 + 2 * (j : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
  have e2 : ((0 : ℕ) : ℝ) + 2 + 2 * (j : ℝ) = 2 * (j : ℝ) + 2 := by push_cast; ring
  rw [e1, e2]

/-- **Telescoping law.**  `A_N(s) + A_{N+1}(s) = (N+1)^{−s}`. -/
theorem dqptAltTail_add_succ {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    dqptAltTail s N + dqptAltTail s (N + 1) = dqptRp s ((N : ℝ) + 1) := by
  set u : ℕ → ℂ := fun j => dqptRp s ((N : ℝ) + 1 + 2 * j) with hu
  have hterm : ∀ j : ℕ, dqptAltTailTerm s N j + dqptAltTailTerm s (N + 1) j = u j - u (j + 1) := by
    intro j
    rw [dqptAltTailTerm, dqptAltTailTerm, hu]
    simp only
    have e2 : (((N + 1 : ℕ) : ℝ) + 1 + 2 * j) = ((N : ℝ) + 2 + 2 * j) := by push_cast; ring
    have e3 : (((N + 1 : ℕ) : ℝ) + 2 + 2 * j) = ((N : ℝ) + 1 + 2 * ((j : ℝ) + 1)) := by
      push_cast; ring
    have e4 : ((N : ℝ) + 1 + 2 * ((j + 1 : ℕ) : ℝ)) = ((N : ℝ) + 1 + 2 * ((j : ℝ) + 1)) := by
      push_cast; ring
    rw [e2, e3, e4]
    ring
  have hsum : Summable (fun j : ℕ => u j - u (j + 1)) := by
    refine ((summable_dqptAltTailTerm hs N).add (summable_dqptAltTailTerm hs (N + 1))).congr ?_
    intro j; exact hterm j
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have hnorm : ∀ j : ℕ, ‖u j‖ = ((N : ℝ) + 1 + 2 * j) ^ (-s.re) := by
      intro j; exact dqptRp_norm (by positivity)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr (fun j => (hnorm j).symm) ?_
    have h2j : Tendsto (fun j : ℕ => 2 * (j : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
    have hbase : Tendsto (fun j : ℕ => (N : ℝ) + 1 + 2 * (j : ℝ)) atTop atTop :=
      Filter.tendsto_atTop_add_const_left _ ((N : ℝ) + 1) h2j
    exact (tendsto_rpow_neg_atTop hs).comp hbase
  have hpartial : ∀ n : ℕ, ∑ j ∈ Finset.range n, (u j - u (j + 1)) = u 0 - u n :=
    fun n => Finset.sum_range_sub' u n
  have htend : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, (u j - u (j + 1))) atTop (𝓝 (u 0)) := by
    refine Tendsto.congr (fun n => (hpartial n).symm) ?_
    have hc : Tendsto (fun _ : ℕ => u 0) atTop (𝓝 (u 0)) := tendsto_const_nhds
    simpa using hc.sub hu0
  have hhas : HasSum (fun j : ℕ => u j - u (j + 1)) (u 0) :=
    (hsum.hasSum_iff_tendsto_nat).mpr htend
  have hfinal : ∑' j : ℕ, (u j - u (j + 1)) = u 0 := hhas.tsum_eq
  rw [dqptAltTail, dqptAltTail,
    ← (summable_dqptAltTailTerm hs N).tsum_add (summable_dqptAltTailTerm hs (N + 1)),
    tsum_congr hterm, hfinal, hu]
  norm_num

/-! ## The exact finite-`N` decomposition -/

/-- **Supplementary Note 1, the exact decomposition.**  For `Re s > 0` and `s ≠ 1`,
`(1 − 2^{1−s})·ζ(s) = S_N(s) + (−1)^N A_N(s)`.  Equivalently `R_N(s) = (−1)^N A_N(s)` for the
conditionally convergent tail of the paper. -/
theorem dqptEta_eq_altPartialSum_add_tail {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
      = dqptAltPartialSum s N + (-1 : ℂ) ^ N * dqptAltTail s N := by
  induction N with
  | zero => simpa [dqptAltTail_zero] using (etaPair_eq s hs hs1).symm
  | succ N ih =>
      have htel := dqptAltTail_add_succ hs N
      have hsucc : dqptAltTail s (N + 1) = dqptRp s ((N : ℝ) + 1) - dqptAltTail s N := by
        linear_combination htel
      rw [dqptAltPartialSum_succ, hsucc, pow_succ]
      rw [ih]
      ring

end

end RHTower.DQPT
