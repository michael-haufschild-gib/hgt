import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfVitaliCriterion

/-!
# Infinite-order Laplace criterion for the convolution half

Retain every canonical convolution-half coefficient and damp index `n` by
`exp (-n / (N + 1))`. Each positive-time sum is entire, while dominated convergence recovers the
canonical `LSeries` pointwise on `Re s > 1` as damping disappears. After the existing pole and
Carleman normalizations, Vitali reduces the first parity rung to local boundedness of this explicit
infinite-order arithmetic family.

This module proves the construction and conditional bridge. It does not assert local boundedness.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive damping scale tending to zero. -/
def squarefreeHalfLaplaceScale (N : ℕ) : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹

theorem squarefreeHalfLaplaceScale_pos (N : ℕ) :
    0 < squarefreeHalfLaplaceScale N := by
  dsimp [squarefreeHalfLaplaceScale]
  positivity

/-- Exponentially damped canonical convolution-half term. -/
def squarefreeHalfLaplaceTerm (N : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(((n : ℝ) * squarefreeHalfLaplaceScale N : ℝ) : ℂ)) *
    LSeries.term squarefreeConvolutionHalf s n

/-- Infinite-order arithmetic heat smoothing of the canonical convolution half. -/
def squarefreeHalfLaplaceSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, squarefreeHalfLaplaceTerm N s n

private theorem LSeries_term_differentiable_laplace (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (fun s : ℂ => LSeries.term a s n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [LSeries.term_zero] using (differentiable_const (c := (0 : ℂ)))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hfun : (fun s : ℂ => LSeries.term a s n) =
        fun s : ℂ => a n * (n : ℂ) ^ (-s) := by
      funext s
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
    rw [hfun]
    intro s
    exact (differentiableAt_const _).mul
      (DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id.neg
        (Complex.ofReal_mem_slitPlane.mpr hnpos))

private theorem differentiable_squarefreeHalfLaplaceTerm (N n : ℕ) :
    Differentiable ℂ (fun s : ℂ => squarefreeHalfLaplaceTerm N s n) := by
  exact (differentiable_const (c :=
    Complex.exp (-(((n : ℝ) * squarefreeHalfLaplaceScale N : ℝ) : ℂ)))).mul
      (LSeries_term_differentiable_laplace _ n)

/-- Every fixed positive-time Laplace smoothing is entire. -/
theorem analyticOnNhd_squarefreeHalfLaplaceSum (N : ℕ) :
    AnalyticOnNhd ℂ (squarefreeHalfLaplaceSum N) Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s₀
  let M : ℕ := Nat.ceil |s₀.re| + 2
  let U : Set ℂ := Metric.ball s₀ 1
  let u : ℕ → ℝ := fun n =>
    (n : ℝ) ^ (M + 1) *
      Real.exp (-((n : ℝ) * squarefreeHalfLaplaceScale N))
  have hu : Summable u := by
    simpa [u, mul_comm] using
      (Real.summable_pow_mul_exp_neg_nat_mul (M + 1)
        (squarefreeHalfLaplaceScale_pos N))
  have hbound : ∀ n : ℕ, ∀ w ∈ U,
      ‖squarefreeHalfLaplaceTerm N w n‖ ≤ u n := by
    intro n w hw
    by_cases hn : n = 0
    · subst n
      simp [squarefreeHalfLaplaceTerm, u]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hdist : ‖w - s₀‖ < 1 := by
      simpa [U, Complex.dist_eq] using hw
    have hre : |w.re - s₀.re| < 1 :=
      lt_of_le_of_lt (Complex.abs_re_le_norm (w - s₀)) hdist
    have hwLower : -w.re ≤ |s₀.re| + 1 := by
      have hleft := (abs_lt.mp hre).1
      have hsabs : -s₀.re ≤ |s₀.re| := neg_le_abs s₀.re
      linarith
    have hceil : |s₀.re| ≤ (Nat.ceil |s₀.re| : ℝ) := Nat.le_ceil _
    have hM : -w.re ≤ (M : ℝ) := by
      dsimp [M]
      push_cast
      linarith
    have hpow : (n : ℝ) ^ (-w.re) ≤ (n : ℝ) ^ (M : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 hM
    have hcoeff : ‖squarefreeConvolutionHalf n‖ ≤ (n : ℝ) :=
      (norm_squarefreeConvolutionHalf_le_card_divisors hn).trans
        (by exact_mod_cast Nat.card_divisors_le_self n)
    have hterm : ‖LSeries.term squarefreeConvolutionHalf w n‖ ≤
        (n : ℝ) ^ (M + 1) := by
      rw [LSeries.norm_term_eq, if_neg hn]
      rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
      calc
        ‖squarefreeConvolutionHalf n‖ * (n : ℝ) ^ (-w.re) ≤
            (n : ℝ) * (n : ℝ) ^ (M : ℝ) :=
          mul_le_mul hcoeff hpow (Real.rpow_nonneg hnpos.le _)
            (by positivity)
        _ = (n : ℝ) ^ (M + 1) := by
          rw [Real.rpow_natCast]
          ring
    rw [squarefreeHalfLaplaceTerm, norm_mul, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    dsimp [u]
    calc
      Real.exp (-((n : ℝ) * squarefreeHalfLaplaceScale N)) *
          ‖LSeries.term squarefreeConvolutionHalf w n‖ ≤
          Real.exp (-((n : ℝ) * squarefreeHalfLaplaceScale N)) *
            (n : ℝ) ^ (M + 1) :=
        mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
      _ = (n : ℝ) ^ (M + 1) *
          Real.exp (-((n : ℝ) * squarefreeHalfLaplaceScale N)) := by ring
  have hdiff : DifferentiableOn ℂ (squarefreeHalfLaplaceSum N) U := by
    unfold squarefreeHalfLaplaceSum
    exact Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n => (differentiable_squarefreeHalfLaplaceTerm N n).differentiableOn)
      Metric.isOpen_ball hbound
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

theorem tendsto_squarefreeHalfLaplaceScale_zero :
    Tendsto squarefreeHalfLaplaceScale atTop (nhds 0) := by
  have hden : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  convert hden.inv_tendsto_atTop using 1
  ext N
  simp [squarefreeHalfLaplaceScale]

private theorem tendsto_squarefreeHalfLaplaceTerm_undamped (s : ℂ) (n : ℕ) :
    Tendsto (fun N => squarefreeHalfLaplaceTerm N s n) atTop
      (nhds (LSeries.term squarefreeConvolutionHalf s n)) := by
  have hargReal : Tendsto
      (fun N => -((n : ℝ) * squarefreeHalfLaplaceScale N)) atTop (nhds 0) := by
    simpa using (tendsto_squarefreeHalfLaplaceScale_zero.const_mul (n : ℝ)).neg
  have harg : Tendsto
      (fun N => ((-((n : ℝ) * squarefreeHalfLaplaceScale N) : ℝ) : ℂ))
      atTop (nhds 0) := hargReal.ofReal
  have hexp : Tendsto
      (fun N => Complex.exp (-(((n : ℝ) * squarefreeHalfLaplaceScale N : ℝ) : ℂ)))
      atTop (nhds 1) := by
    have h := Complex.continuous_exp.continuousAt.tendsto.comp harg
    refine (show Tendsto
      (Complex.exp ∘ fun N =>
        ((-((n : ℝ) * squarefreeHalfLaplaceScale N) : ℝ) : ℂ))
      atTop (nhds 1) from by simpa only [Complex.exp_zero] using h).congr' ?_
    filter_upwards with K
    simp only [Function.comp_apply]
    congr 1
    norm_cast
  simpa [squarefreeHalfLaplaceTerm] using
    hexp.mul_const (LSeries.term squarefreeConvolutionHalf s n)

/-- Damping disappears at every point of the absolute Euler chamber. -/
theorem tendsto_squarefreeHalfLaplaceSum {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => squarefreeHalfLaplaceSum N s) atTop
      (nhds (LSeries squarefreeConvolutionHalf s)) := by
  have hmajor : Summable
      (fun n => ‖LSeries.term squarefreeConvolutionHalf s n‖) :=
    (LSeriesSummable_squarefreeConvolutionHalf hs).norm
  have hdom : ∀ᶠ N in atTop, ∀ n,
      ‖squarefreeHalfLaplaceTerm N s n‖ ≤
        ‖LSeries.term squarefreeConvolutionHalf s n‖ := by
    filter_upwards with N n
    rw [squarefreeHalfLaplaceTerm, norm_mul, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hnonneg : 0 ≤ (n : ℝ) * squarefreeHalfLaplaceScale N :=
      mul_nonneg (Nat.cast_nonneg n) (squarefreeHalfLaplaceScale_pos N).le
    have hexp : Real.exp (-((n : ℝ) * squarefreeHalfLaplaceScale N)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    simpa using mul_le_of_le_one_left (norm_nonneg _) hexp
  have hlim := tendsto_tsum_of_dominated_convergence hmajor
    (fun n => tendsto_squarefreeHalfLaplaceTerm_undamped s n) hdom
  simpa [squarefreeHalfLaplaceSum, LSeries] using hlim

/-- Pole-cleared Laplace approximants retaining all arithmetic coefficients. -/
def poleClearedFirstTraceLaplaceApprox (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox N s * squarefreeHalfLaplaceSum N s /
    squarefreeCarlemanHalfDet s

theorem analyticOnNhd_poleClearedFirstTraceLaplaceApprox_rightHalf (N : ℕ) :
    AnalyticOnNhd ℂ (poleClearedFirstTraceLaplaceApprox N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf N).mul
    ((analyticOnNhd_squarefreeHalfLaplaceSum N).mono (Set.subset_univ _)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

theorem tendsto_poleClearedFirstTraceLaplaceApprox {s : ℂ} (hs : s ∈ farHalf) :
    Tendsto (fun N => poleClearedFirstTraceLaplaceApprox N s) atTop
      (nhds (poleClearedFirstTraceSourceLimit s)) := by
  have hp := tendstoLocallyUniformlyOn_poleFactorSqrtApprox.tendsto_at hs
  have hL := tendsto_squarefreeHalfLaplaceSum (mem_farHalf.mp hs)
  simpa [poleClearedFirstTraceLaplaceApprox, poleClearedFirstTraceSourceLimit] using
    (hp.mul hL).div_const (squarefreeCarlemanHalfDet s)

/-- Local boundedness obligation for the explicit infinite-order Laplace family. -/
def PoleClearedFirstTraceLaplaceLocallyBounded : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R, ‖poleClearedFirstTraceLaplaceApprox N w‖ ≤ C

/-- Local boundedness of the arithmetic Laplace family forces the first parity rung. -/
theorem rhLadder_one_of_poleClearedFirstTraceLaplaceLocallyBounded
    (hloc : PoleClearedFirstTraceLaplaceLocallyBounded) : RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceLaplaceApprox_rightHalf N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        tendsto_poleClearedFirstTraceLaplaceApprox hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      (tendsto_poleClearedFirstTraceLaplaceApprox hs)
  let H : ℂ → ℂ := fun s => G s ^ 2 - poleClearedFirstTraceExponentialContinuation s
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    ((hGdiff.analyticOnNhd isOpen_rightHalf).pow 2).sub
      analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf :=
      isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hmem.mono fun s hs => by
      dsimp [H]
      rw [hGeq hs, poleClearedFirstTraceSourceLimit_sq hs, sub_self]
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have hHall := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_rightHalf.isPreconnected (farHalf_subset_rightHalf two_mem_farHalf) hfreq
  intro s hs
  have hzero := hHall hs
  change G s ^ 2 - poleClearedFirstTraceExponentialContinuation s = 0 at hzero
  exact sub_eq_zero.mp hzero

end

end RHTower
