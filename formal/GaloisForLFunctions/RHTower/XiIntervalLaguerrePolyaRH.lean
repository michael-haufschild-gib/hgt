import GaloisForLFunctions.HTGeometry.EvenRealRootedGaussianBounds
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.HTGeometry.IsingCharRealRootedApprox
import GaloisForLFunctions.RHTower.EntireMontel
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.XiHadamardGrowth

/-!
# Laguerre–Pólya approximation of `Ξ` on one small real interval forces RH

**Theorem** (`riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc`). Let `F_n` be functions in
the Laguerre–Pólya class, i.e. locally uniform limits of real polynomials with only real zeros. If
`F_n → Ξ/Ξ(0)` uniformly on one interval `[−ε, ε]` with `0 < ε`, `ε² ≤ 32`, then RH holds.

In particular (`riemannHypothesis_of_realRooted_tendstoUniformlyOn_Icc`), RH holds as soon as
`Ξ/Ξ(0)` is a uniform limit on `[−ε, ε]` of real polynomials with only real zeros. On that interval
`Ξ` is positive and smooth, so Weierstrass approximation is available. The content is that the
approximants can be taken real-rooted. Every Laguerre–Pólya producer (Ising magnetizations, lossless
stacks, real-rooted ground states) thus only has to reproduce `Ξ` at low frequency.

**Proof.** Put `H_n(z) = F_n(z)F_n(−z)`. It is an even Laguerre–Pólya function, with approximants
`p(X)p(−X)`. Its Gaussian bounds give `|H_n(z)|² ≤ |H_n(0)|² e^{|z|²L_n}` and
`|H_n(ε)|² ≤ |H_n(0)|² e^{−ε²L_n}` before the first zero. Uniform convergence on `[−ε, ε]`, where `Ξ`
does not vanish, keeps `H_n` away from `0` there and bounds `L_n`. Montel gives a subsequence
converging locally uniformly on `ℂ`. Its limit agrees with `Ξ(z)Ξ(−z)/Ξ(0)²` on `[−ε, ε]`, hence
everywhere. Every zero of `Ξ` is then a limit of real zeros of `H_n` (Hurwitz).
-/

open Complex Filter Topology Set Polynomial

namespace RHTower.IntervalLaguerrePolya

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Negating the variable preserves real-rootedness. -/
theorem splits_comp_neg_X (p : ℝ[X]) (hp : p.Splits) : (p.comp (-X)).Splits := by
  by_cases h0 : p = 0
  · rw [h0, zero_comp]; exact Polynomial.Splits.zero
  refine splits_of_forall_complex_root_real _ _ le_rfl fun z hz => ?_
  rw [aeval_comp, map_neg, aeval_X] at hz
  have := im_eq_zero_of_splits hp h0 hz
  rw [Complex.neg_im] at this
  linarith

theorem polyEvalC_comp_neg_X (p : ℝ[X]) (z : ℂ) :
    polyEvalC (p.comp (-X)) z = polyEvalC p (-z) := by
  simp only [polyEvalC, aeval_comp, map_neg, aeval_X]

/-- **Reflected products.** If `F` is Laguerre–Pólya, then `z ↦ F(z)F(−z)` is a locally uniform limit
of even real-rooted real polynomials. -/
theorem exists_even_approx_reflectProduct {F : ℂ → ℂ} (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) :
    ∃ q : ℕ → ℝ[X], (∀ N, (q N).Splits) ∧ (∀ N z, polyEvalC (q N) (-z) = polyEvalC (q N) z) ∧
      TendstoLocallyUniformly (fun N => polyEvalC (q N)) (fun z => F z * F (-z)) atTop := by
  have hFc : Continuous F := hF.differentiable.continuous
  obtain ⟨p, hsplit, hconv⟩ := hF
  refine ⟨fun N => p N * (p N).comp (-X), fun N => (hsplit N).mul (splits_comp_neg_X _ (hsplit N)),
    fun N z => ?_, ?_⟩
  · simp only [polyEvalC_mul, polyEvalC_comp_neg_X, neg_neg]
    ring
  · have hneg := hconv.comp (fun z : ℂ => -z) continuous_neg
    have h := hconv.mul₀ hneg hFc (hFc.comp continuous_neg)
    refine h.congr fun N z => ?_
    simp [polyEvalC_mul, polyEvalC_comp_neg_X, Function.comp_def]

/-- A Laguerre–Pólya function is real on the real axis. -/
theorem im_eq_zero_of_laguerrePolya_ofReal {F : ℂ → ℂ} (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) (t : ℝ) :
    (F t).im = 0 := by
  obtain ⟨p, -, hconv⟩ := hF
  have h := (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ (t : ℂ))
  have him := (Complex.continuous_im.tendsto _).comp h
  have hzero : ∀ N, (polyEvalC (p N) t).im = 0 := fun N => by
    rw [polyEvalC_ofReal, Complex.ofReal_im]
  simp only [Function.comp_def, hzero] at him
  exact (tendsto_nhds_unique tendsto_const_nhds him).symm

/-- **Low-frequency rigidity, window form.** Laguerre–Pólya functions converging uniformly on
`[−ε, ε]` to a continuous nowhere-vanishing limit have reflected products `F(z)F(−z)` converging
locally uniformly on `ℂ` along a subsequence; the entire limit agrees with `G(t)G(−t)` on the
window. -/
theorem exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window {F : ℕ → ℂ → ℂ}
    {G : ℂ → ℂ} (hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya (F n)) {ε : ℝ}
    (hε : 0 < ε) (hGc : ContinuousOn (fun s : ℝ => G s) (Icc (-ε) ε))
    (hGne : ∀ s : ℝ, |s| ≤ ε → G s ≠ 0)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => G t) atTop (Icc (-ε) ε)) :
    ∃ σ : ℕ → ℕ, ∃ g : ℂ → ℂ, Tendsto σ atTop atTop ∧ Differentiable ℂ g ∧
      TendstoLocallyUniformly (fun k z => F (σ k) z * F (σ k) (-z)) g atTop ∧
      ∀ t ∈ Icc (-ε) ε, g t = G t * G (-(t : ℂ)) := by
  set H : ℕ → ℂ → ℂ := fun n z => F n z * F n (-z) with hH
  choose q hqsplit hqeven hqconv using fun n => exists_even_approx_reflectProduct (hLP n)
  -- `G` stays away from zero on the interval
  obtain ⟨c₀, hc₀, hc₀le⟩ : ∃ c₀ > 0, ∀ s ∈ Icc (-ε) ε, c₀ ≤ ‖G s‖ := by
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith : -ε ≤ ε)) hGc.norm
    exact ⟨‖G s₀‖, norm_pos_iff.mpr (hGne s₀ (abs_le.mpr ⟨hs₀.1, hs₀.2⟩)), fun s hs => hmin hs⟩
  have hev : ∀ᶠ n in atTop, ∀ s ∈ Icc (-ε) ε, c₀ / 2 < ‖F n s‖ := by
    have := Metric.tendstoUniformlyOn_iff.mp hconv (c₀ / 2) (by positivity)
    filter_upwards [this] with n hn s hs
    have h1 := hn s hs
    have h2 := hc₀le s hs
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (G s) (F n s)
    linarith
  have h0mem : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hεmem : ε ∈ Icc (-ε) ε := ⟨by linarith, le_rfl⟩
  have hnegmem : ∀ s ∈ Icc (-ε) ε, -s ∈ Icc (-ε) ε := fun s hs => ⟨by linarith [hs.2], by
    linarith [hs.1]⟩
  have hF0 : Tendsto (fun n => F n 0) atTop (𝓝 (G 0)) := by
    have := hconv.tendsto_at h0mem
    simpa using this
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hev.and (hF0.norm.eventually
    (gt_mem_nhds (lt_add_one ‖G 0‖))))
  set C : ℝ := ‖G 0‖ + 1 with hC
  -- the variance bound
  set K : ℝ := 4 / ε ^ 2 * Real.log (2 * C / c₀) with hK
  have hL : ∀ n, n₁ ≤ n → (lagRatio (H n)).re ≤ K := by
    intro n hn
    obtain ⟨hlow, hup⟩ := hn₁ n hn
    have hne : ∀ s : ℝ, |s| ≤ |ε| → H n s ≠ 0 := by
      intro s hs
      rw [abs_of_pos hε] at hs
      have hsm : s ∈ Icc (-ε) ε := abs_le.mp hs
      have h1 := hlow s hsm
      have h2 := hlow (-s) (hnegmem s hsm)
      simp only [hH, push_cast]
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · rw [h, norm_zero] at h1; linarith
      · rw [Complex.ofReal_neg] at h2; rw [h, norm_zero] at h2; linarith
    have hH0 : H n 0 ≠ 0 := by
      have := hne 0 (by rw [abs_zero]; exact abs_nonneg _)
      simpa using this
    have hb := mul_neg_le_of_tendsto_even (hqsplit n) (hqconv n) hH0 hne
    have heven : H n (-(ε : ℂ)) = H n ε := by simp only [hH, neg_neg]; ring
    have hreal : (H n ε).im = 0 := by
      have h1 := im_eq_zero_of_laguerrePolya_ofReal (hLP n) ε
      have h2 := im_eq_zero_of_laguerrePolya_ofReal (hLP n) (-ε)
      simp only [hH, Complex.mul_im]
      rw [show -(ε : ℂ) = ((-ε : ℝ) : ℂ) by push_cast; ring, h1, h2]
      ring
    have hsq : (H n ε * H n (-(ε : ℂ))).re = ‖H n ε‖ ^ 2 := by
      rw [heven, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, hreal]
      ring
    have hb' : (H n ε * H n (-(ε : ℂ))).re ≤
        ‖H n 0‖ ^ 2 * Real.exp (-(ε ^ 2 * (lagRatio (H n)).re)) := hb
    rw [hsq] at hb'
    -- `‖H n ε‖ ≥ (c₀/2)²` and `‖H n 0‖ ≤ C²`
    have hHε : (c₀ / 2) ^ 2 ≤ ‖H n ε‖ := by
      simp only [hH, norm_mul]
      have h1 := hlow ε hεmem
      have h2 := hlow (-ε) (hnegmem ε hεmem)
      rw [Complex.ofReal_neg] at h2
      rw [sq]
      exact mul_le_mul h1.le h2.le (by positivity) (norm_nonneg _)
    have hH0le : ‖H n 0‖ ≤ C ^ 2 := by
      rw [show H n 0 = F n 0 ^ 2 by simp [hH, sq], norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using hup.le) 2
    have hc2 : 0 < (c₀ / 2) ^ 2 := by positivity
    have hkey : ((c₀ / 2) ^ 2) ^ 2 ≤ (C ^ 2) ^ 2 * Real.exp (-(ε ^ 2 * (lagRatio (H n)).re)) := by
      calc ((c₀ / 2) ^ 2) ^ 2 ≤ ‖H n ε‖ ^ 2 := pow_le_pow_left₀ hc2.le hHε 2
        _ ≤ ‖H n 0‖ ^ 2 * Real.exp (-(ε ^ 2 * (lagRatio (H n)).re)) := hb'
        _ ≤ (C ^ 2) ^ 2 * Real.exp (-(ε ^ 2 * (lagRatio (H n)).re)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hH0le 2)
              (Real.exp_pos _).le
    have hC0 : 0 < C := by rw [hC]; positivity
    have hlog := Real.log_le_log (by positivity) hkey
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
    have e1 : Real.log (((c₀ / 2) ^ 2) ^ 2) = 4 * Real.log (c₀ / 2) := by
      rw [← pow_mul, Real.log_pow]; norm_num
    have e2 : Real.log ((C ^ 2) ^ 2) = 4 * Real.log C := by
      rw [← pow_mul, Real.log_pow]; norm_num
    have e3 : Real.log (2 * C / c₀) = Real.log C - Real.log (c₀ / 2) := by
      rw [show 2 * C / c₀ = C / (c₀ / 2) by field_simp, Real.log_div hC0.ne' (by positivity)]
    rw [e1, e2] at hlog
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [hK, e3, div_mul_eq_mul_div, le_div_iff₀ hε2]
    nlinarith
  -- uniform bounds and Montel
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp hev
  set n₀ : ℕ := max n₁ n₂ with hn₀
  set ψ : ℕ → ℂ → ℂ := fun k => H (k + n₀) with hψ
  have hψdiff : ∀ k, Differentiable ℂ (ψ k) := fun k =>
    ((hLP (k + n₀)).differentiable).mul ((hLP (k + n₀)).differentiable.comp differentiable_neg)
  have hbd : ∀ R : ℝ, ∃ B : ℝ, ∀ k, ∀ z ∈ Metric.ball (0 : ℂ) R, ‖ψ k z‖ ≤ B := by
    intro R
    refine ⟨C ^ 2 * Real.exp (R ^ 2 * max K 0), fun k z hz => ?_⟩
    have hzR : ‖z‖ ≤ R := by have := mem_ball_zero_iff.mp hz; linarith
    have hn : n₁ ≤ k + n₀ := by omega
    obtain ⟨hlow, hup⟩ := hn₁ (k + n₀) hn
    have hH0 : H (k + n₀) 0 ≠ 0 := by
      simp only [hH, neg_zero]
      have h1 := hlow 0 h0mem
      intro h
      rw [Complex.ofReal_zero] at h1
      rcases mul_self_eq_zero.mp h with h'
      rw [h', norm_zero] at h1; linarith
    have hg := norm_sq_le_of_tendsto_even (hqsplit (k + n₀)) (hqeven (k + n₀)) (hqconv (k + n₀))
      hH0 z
    have hH0le : ‖H (k + n₀) 0‖ ≤ C ^ 2 := by
      rw [show H (k + n₀) 0 = F (k + n₀) 0 ^ 2 by simp [hH, sq], norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using hup.le) 2
    have hLk := hL (k + n₀) hn
    have h1 : ‖z‖ ^ 2 * (lagRatio (H (k + n₀))).re ≤ R ^ 2 * max K 0 := by
      have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
      calc ‖z‖ ^ 2 * (lagRatio (H (k + n₀))).re ≤ ‖z‖ ^ 2 * max K 0 :=
            mul_le_mul_of_nonneg_left (hLk.trans (le_max_left _ _)) (by positivity)
        _ ≤ R ^ 2 * max K 0 := mul_le_mul_of_nonneg_right hz2 (le_max_right _ _)
    set X : ℝ := Real.exp (R ^ 2 * max K 0) with hX
    have hX1 : 1 ≤ X := Real.one_le_exp (by positivity)
    have h2 : ‖ψ k z‖ ^ 2 ≤ (C ^ 2) ^ 2 * X := by
      calc ‖ψ k z‖ ^ 2 ≤ ‖H (k + n₀) 0‖ ^ 2 * Real.exp (‖z‖ ^ 2 * (lagRatio (H (k + n₀))).re) := hg
        _ ≤ (C ^ 2) ^ 2 * X :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hH0le 2) (Real.exp_le_exp.mpr h1)
              (Real.exp_pos _).le (by positivity)
    have h3 : (C ^ 2) ^ 2 * X ≤ (C ^ 2 * X) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hB0 : 0 ≤ C ^ 2 * X := by positivity
    nlinarith [norm_nonneg (ψ k z)]
  obtain ⟨σ, g, hσ, hgconv⟩ := RHTower.exists_subseq_tendstoLocallyUniformly hψdiff hbd
  have hgdiff : Differentiable ℂ g := by
    rw [← differentiableOn_univ]
    exact (tendstoLocallyUniformlyOn_univ.2 hgconv).differentiableOn
      (Eventually.of_forall fun k => (hψdiff (σ k)).differentiableOn) isOpen_univ
  have hidx : Tendsto (fun k => σ k + n₀) atTop atTop :=
    (tendsto_add_atTop_nat n₀).comp hσ.tendsto_atTop
  -- identification on the interval
  have hgint : ∀ t ∈ Icc (-ε) ε, g t = G t * G (-(t : ℂ)) := by
    intro t ht
    have h1 := (tendstoLocallyUniformlyOn_univ.2 hgconv).tendsto_at (mem_univ (t : ℂ))
    have hp := (hconv.tendsto_at ht).comp hidx
    have hm := (hconv.tendsto_at (hnegmem t ht)).comp hidx
    have h2 : Tendsto (fun k => ψ (σ k) t) atTop (𝓝 (G t * G (-(t : ℂ)))) := by
      have := hp.mul hm
      simp only [Function.comp_def, Complex.ofReal_neg] at this
      simpa [hψ, hH] using this
    exact tendsto_nhds_unique h1 h2
  exact ⟨fun k => σ k + n₀, g, hidx, hgdiff, hgconv, hgint⟩

/-- **Low-frequency rigidity of the Laguerre–Pólya class.** If Laguerre–Pólya functions `F_n`
converge uniformly on `[−ε, ε]` to an entire `G` without zeros there, then along a subsequence
`F_n(z)F_n(−z) → G(z)G(−z)` locally uniformly on `ℂ`. -/
theorem exists_subseq_reflectProduct_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya (F n)) (hG : Differentiable ℂ G) {ε : ℝ} (hε : 0 < ε)
    (hGne : ∀ s : ℝ, |s| ≤ ε → G s ≠ 0)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => G t) atTop (Icc (-ε) ε)) :
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧
      TendstoLocallyUniformly (fun k z => F (σ k) z * F (σ k) (-z)) (fun z => G z * G (-z))
        atTop := by
  obtain ⟨σ, g, hσ, hgdiff, hgconv, hgint⟩ :=
    exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window hLP hε
      (hG.continuous.comp Complex.continuous_ofReal).continuousOn hGne hconv
  have hgG : g = fun z => G z * G (-z) := by
    have hGan : AnalyticOnNhd ℂ (fun z => G z * G (-z)) univ := fun z _ =>
      (hG.mul (hG.comp differentiable_neg)).analyticAt z
    have hgan : AnalyticOnNhd ℂ g univ := fun z _ => hgdiff.analyticAt z
    have hseq : Tendsto (fun k : ℕ => ((ε / (k + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
        rw [mul_zero] at h
        have := (Complex.continuous_ofReal.tendsto 0).comp h
        simpa [Function.comp_def, div_eq_mul_inv] using this
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    have hmem : ∀ k : ℕ, ε / (k + 1) ∈ Icc (-ε) ε := by
      intro k
      have hk : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      constructor
      · have : 0 ≤ ε / (k + 1) := by positivity
        linarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = G z * G (-z) :=
      hseq.frequently (Frequently.of_forall fun k => hgint _ (hmem k))
    funext z
    exact hgan.eqOn_of_preconnected_of_frequently_eq hGan isPreconnected_univ (mem_univ 0)
      hfreq (mem_univ z)
  refine ⟨σ, hσ, ?_⟩
  rw [← hgG]
  exact hgconv

/-- `Ξ` has no zero on `[−√32, √32]`. -/
theorem xiRatio_ne_zero_of_sq_le {s : ℝ} (hs : s ^ 2 ≤ 32) : XiC s / XiC 0 ≠ 0 := by
  refine div_ne_zero ?_ XiC_zero_ne
  intro h0
  apply xi_ne_zero_of_im_sq_le (s := 1 / 2 + (s : ℂ) * I) ?_
  · exact h0
  · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    norm_num
    exact hs

/-- **Laguerre–Pólya approximation on one interval forces RH.** -/
theorem riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc {F : ℕ → ℂ → ℂ}
    (hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya (F n)) {ε : ℝ} (hε : 0 < ε) (hε32 : ε ^ 2 ≤ 32)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => XiC t / XiC 0) atTop
      (Icc (-ε) ε)) :
    RiemannHypothesis := by
  set G : ℂ → ℂ := fun z => XiC z / XiC 0 with hG
  have hX0 := XiC_zero_ne
  have hGdiff : Differentiable ℂ G := fun z =>
    ((XiC_analytic z (mem_univ z)).div_const).differentiableAt
  have hGne : ∀ s : ℝ, |s| ≤ ε → G s ≠ 0 := by
    intro s hs
    refine xiRatio_ne_zero_of_sq_le ?_
    have : s ^ 2 ≤ ε ^ 2 := by
      rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
    linarith
  obtain ⟨σ, hσ, hloc⟩ := exists_subseq_reflectProduct_tendstoLocallyUniformly hLP hGdiff hε hGne
    hconv
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hlimAn : AnalyticOnNhd ℂ (fun w => G w * G (-w)) univ := fun w _ =>
    (hGdiff.mul (hGdiff.comp differentiable_neg)).analyticAt w
  have hlim0 : G 0 * G (-0) ≠ 0 := by
    rw [neg_zero]; exact mul_ne_zero (div_ne_zero hX0 hX0) (div_ne_zero hX0 hX0)
  have hlimz : G z * G (-z) = 0 := by simp only [hG, hXiC, zero_div, zero_mul]
  have hev0 : ∀ᶠ k in atTop, F (σ k) 0 * F (σ k) (-0) ≠ 0 := by
    have h := (tendstoLocallyUniformlyOn_univ.2 hloc).tendsto_at (mem_univ (0 : ℂ))
    exact h.eventually_ne hlim0
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hloc hlimAn
    (Eventually.of_forall fun k =>
      ((hLP (σ k)).differentiable).mul ((hLP (σ k)).differentiable.comp differentiable_neg))
    (isClosed_eq Complex.continuous_im continuous_const)
    (by
      filter_upwards [hev0] with k hk w hw
      obtain ⟨q, hqs, -, hqc⟩ := exists_even_approx_reflectProduct (hLP (σ k))
      exact GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya ⟨q, hqs, hqc⟩ hk hw)
    hlim0 hlimz
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) (by linarith)

/-- **Real-rooted polynomial approximation of `Ξ` on one small interval forces RH.** If real
polynomials with only real zeros converge to `Ξ/Ξ(0)` uniformly on `[−ε, ε]` (`0 < ε`,
`ε² ≤ 32`), then RH holds. -/
theorem riemannHypothesis_of_realRooted_tendstoUniformlyOn_Icc {p : ℕ → ℝ[X]}
    (hsplit : ∀ n, (p n).Splits) {ε : ℝ} (hε : 0 < ε) (hε32 : ε ^ 2 ≤ 32)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-ε) ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc
    (fun n => ⟨fun _ => p n, fun _ => hsplit n, Metric.tendstoLocallyUniformly_iff.2
      fun δ hδ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => by simpa using hδ⟩⟩)
    hε hε32 hconv

/-- **Converse under RH.** The paired divisor polynomials of `Ξ` converge to `Ξ/Ξ(0)` uniformly on
every compact real interval. -/
theorem exists_realRooted_tendstoUniformlyOn_Icc_of_rh (hRH : RiemannHypothesis) (ε : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ n, (p n).Splits) ∧
      TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t) (fun t : ℝ => XiC t / XiC 0) atTop
        (Icc (-ε) ε) := by
  refine ⟨fun n => xiPairedPolynomial (xiSupportExhaustionFinset n),
    fun n => xiPairedPolynomial_splits _, ?_⟩
  have hloc : TendstoLocallyUniformlyOn (fun n => xiPairedE1Product (xiSupportExhaustionFinset n))
      xiCanonicalProduct atTop univ := by
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := xiPairedE1Product_tendstoLocallyUniformlyOn u hu x hx
    exact ⟨t, ht, xiSupportExhaustionFinset_tendsto_atTop.eventually hev⟩
  have hK : IsCompact ((fun t : ℝ => (t : ℂ)) '' Icc (-ε) ε) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hloc _
    (subset_univ _) hK
  have hcomp := hunif.comp (fun t : ℝ => (t : ℂ))
  have hmono : Icc (-ε) ε ⊆ (fun t : ℝ => (t : ℂ)) ⁻¹' ((fun t : ℝ => (t : ℂ)) '' Icc (-ε) ε) :=
    fun t ht => ⟨t, ht, rfl⟩
  have h := hcomp.mono hmono
  have hX0 := XiC_zero_ne
  have hlim : ∀ t : ℝ, xiCanonicalProduct (t : ℂ) = XiC t / XiC 0 := by
    intro t
    have e := congrFun XiC_eq_constant_mul_canonicalProduct (t : ℂ)
    simp only [Pi.mul_apply] at e
    rw [e, mul_div_cancel_left₀ _ hX0]
  refine (h.congr ?_).congr_right ?_
  · refine Eventually.of_forall fun n t _ => ?_
    simp only [Function.comp_def]
    rw [polyEvalC_ofReal, xiPairedPolynomial_eval_eq_product_of_rh hRH]
  · intro t _
    simp only [Function.comp_def]
    exact hlim t

/-- **RH as low-frequency real-rooted approximability.** For every `ε` with `0 < ε`, `ε² ≤ 32`: RH
holds iff `Ξ/Ξ(0)` is a uniform limit on `[−ε, ε]` of real polynomials with only real zeros. -/
theorem riemannHypothesis_iff_exists_realRooted_tendstoUniformlyOn_Icc {ε : ℝ} (hε : 0 < ε)
    (hε32 : ε ^ 2 ≤ 32) :
    RiemannHypothesis ↔ ∃ p : ℕ → ℝ[X], (∀ n, (p n).Splits) ∧
      TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t) (fun t : ℝ => XiC t / XiC 0) atTop
        (Icc (-ε) ε) :=
  ⟨fun hRH => exists_realRooted_tendstoUniformlyOn_Icc_of_rh hRH ε,
    fun ⟨_, hs, hc⟩ => riemannHypothesis_of_realRooted_tendstoUniformlyOn_Icc hs hε hε32 hc⟩

/-- **Ising magnetizations matching `Ξ` at low frequency force RH.** If the characteristic functions
of zero-field ferromagnetic Ising magnetizations (`J ≥ 0`, `c ≥ 0`) converge to `Ξ/Ξ(0)` uniformly on
one interval `[−ε, ε]`, then RH holds. -/
theorem riemannHypothesis_of_isingCharFn_tendstoUniformlyOn_Icc
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    {ε : ℝ} (hε : 0 < ε) (hε32 : ε ^ 2 ≤ 32)
    (hconv : TendstoUniformlyOn
      (fun n (t : ℝ) => LeeYang.isingCharFn (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-ε) ε)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_Icc (fun n => ?_) hε hε32 hconv
  obtain ⟨q, hs, -, hq⟩ := LeeYang.exists_even_realRooted_approx (J n) (E n) (c n) (hJ n) (hc n)
  exact ⟨q, hs, hq⟩

end

end RHTower.IntervalLaguerrePolya
