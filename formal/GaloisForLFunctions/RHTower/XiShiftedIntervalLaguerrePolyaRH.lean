import GaloisForLFunctions.RHTower.XiIntervalLaguerrePolyaRH
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Real-rooted approximation of `Ξ` on any real interval decides RH

**Theorem** (`riemannHypothesis_iff_exists_realRooted_tendstoUniformlyOn_any`). Take any real
interval `[c − ε, c + ε]` with `ε > 0`. RH holds iff `Ξ` is a uniform limit on that interval of real
polynomials with only real zeros.

The interval may sit anywhere on the real line, at arbitrary height, and may contain zeros of `Ξ`.
The location of every zero of `Ξ` is encoded in real-rooted approximability on any one window.

**Proof.** Translating by `c` preserves real-rootedness. So `F_n(c + z)` are Laguerre–Pólya, and the
low-frequency rigidity (`exists_subseq_reflectProduct_tendstoLocallyUniformly`) gives, along a
subsequence, `F_n(c + z)F_n(c − z) → Ξ(c + z)Ξ(c − z)` locally uniformly on `ℂ`. A non-real zero `ρ`
of `Ξ` would make `z = ρ − c` a zero of the limit that is not real, while every zero of every
`F_n(c + z)F_n(c − z)` is real. Hurwitz excludes this. This needs `Ξ ≠ 0` on the window. A general
window contains a zero-free subwindow, because `Ξ` cannot vanish on a set accumulating at a real
point without vanishing identically (`exists_zeroFree_subwindow`).
-/

open Complex Filter Topology Set Polynomial

namespace RHTower.IntervalLaguerrePolya

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translation by a real number preserves real-rootedness. -/
theorem splits_comp_X_add_C (p : ℝ[X]) (hp : p.Splits) (c : ℝ) : (p.comp (X + C c)).Splits := by
  by_cases h0 : p = 0
  · rw [h0, zero_comp]; exact Polynomial.Splits.zero
  refine splits_of_forall_complex_root_real _ _ le_rfl fun z hz => ?_
  rw [aeval_comp, map_add, aeval_X, aeval_C, Complex.coe_algebraMap] at hz
  have := im_eq_zero_of_splits hp h0 hz
  rw [Complex.add_im, Complex.ofReal_im, add_zero] at this
  exact this

theorem polyEvalC_comp_X_add_C (p : ℝ[X]) (c : ℝ) (z : ℂ) :
    polyEvalC (p.comp (X + C c)) z = polyEvalC p (z + c) := by
  simp only [polyEvalC, aeval_comp, map_add, aeval_X, aeval_C, Complex.coe_algebraMap]

/-- **Translates of Laguerre–Pólya functions.** -/
theorem laguerrePolya_comp_add {F : ℂ → ℂ} (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F)
    (c : ℝ) : GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => F (c + z)) := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  refine ⟨fun n => (p n).comp (X + C c), fun n => splits_comp_X_add_C _ (hsplit n) c, ?_⟩
  have h := hconv.comp (fun z : ℂ => (c : ℂ) + z) (continuous_const.add continuous_id)
  refine h.congr fun n z => ?_
  simp only [Function.comp_def, polyEvalC_comp_X_add_C, add_comm]

/-- **Real-rooted approximation on any zero-free window forces RH.** -/
theorem riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_shifted {F : ℕ → ℂ → ℂ}
    (hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya (F n)) {c ε : ℝ} (hε : 0 < ε)
    (hne : ∀ s ∈ Icc (c - ε) (c + ε), XiC s ≠ 0)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => XiC t) atTop
      (Icc (c - ε) (c + ε))) :
    RiemannHypothesis := by
  set G : ℂ → ℂ := fun z => XiC (c + z) with hG
  have hXdiff : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hGdiff : Differentiable ℂ G := hXdiff.comp (differentiable_const _ |>.add differentiable_id)
  have hmaps : ∀ t ∈ Icc (-ε) ε, c + t ∈ Icc (c - ε) (c + ε) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hGne : ∀ s : ℝ, |s| ≤ ε → G s ≠ 0 := by
    intro s hs
    have := hne (c + s) (hmaps s (abs_le.mp hs))
    simpa [hG] using this
  have hconv' : TendstoUniformlyOn (fun n (t : ℝ) => F n (c + t)) (fun t : ℝ => G t) atTop
      (Icc (-ε) ε) := by
    have h := (hconv.comp (fun t : ℝ => c + t)).mono (fun t ht => hmaps t ht)
    refine (h.congr (Eventually.of_forall fun n t _ => ?_)).congr_right fun t _ => ?_
    · simp
    · simp [hG]
  obtain ⟨σ, hσ, hloc⟩ := exists_subseq_reflectProduct_tendstoLocallyUniformly
    (fun n => laguerrePolya_comp_add (hLP n) c) hGdiff hε hGne hconv'
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro ρ hρ
  by_contra hρim
  set z : ℂ := ρ - c with hz
  have hlimAn : AnalyticOnNhd ℂ (fun w => G w * G (-w)) univ := fun w _ =>
    (hGdiff.mul (hGdiff.comp differentiable_neg)).analyticAt w
  have hG0 : G 0 * G (-0) ≠ 0 := by
    rw [neg_zero]
    have h := hGne 0 (by rw [abs_zero]; exact hε.le)
    exact mul_ne_zero (by simpa using h) (by simpa using h)
  have hlimz : G z * G (-z) = 0 := by
    have : G z = 0 := by simp only [hG, hz]; rw [show (c : ℂ) + (ρ - c) = ρ by ring]; exact hρ
    rw [this, zero_mul]
  have hev0 : ∀ᶠ k in atTop, F (σ k) (c + 0) * F (σ k) (c + -0) ≠ 0 := by
    have h := (tendstoLocallyUniformlyOn_univ.2 hloc).tendsto_at (mem_univ (0 : ℂ))
    exact h.eventually_ne hG0
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hloc hlimAn
    (Eventually.of_forall fun k =>
      ((laguerrePolya_comp_add (hLP (σ k)) c).differentiable).mul
        ((laguerrePolya_comp_add (hLP (σ k)) c).differentiable.comp differentiable_neg))
    (isClosed_eq Complex.continuous_im continuous_const)
    (by
      filter_upwards [hev0] with k hk w hw
      obtain ⟨q, hqs, -, hqc⟩ :=
        exists_even_approx_reflectProduct (laguerrePolya_comp_add (hLP (σ k)) c)
      exact GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya ⟨q, hqs, hqc⟩ hk hw)
    hG0 hlimz
  apply hρim
  rw [hz, Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  exact him

/-- Under RH, `Ξ` is a uniform limit of real-rooted real polynomials on every real interval. -/
theorem exists_realRooted_tendstoUniformlyOn_shifted_of_rh (hRH : RiemannHypothesis) (c ε : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ n, (p n).Splits) ∧
      TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t) (fun t : ℝ => XiC t) atTop
        (Icc (c - ε) (c + ε)) := by
  obtain ⟨p, hsplit, hconv⟩ := exists_realRooted_tendstoUniformlyOn_Icc_of_rh hRH (|c| + |ε|)
  have hsub : Icc (c - ε) (c + ε) ⊆ Icc (-(|c| + |ε|)) (|c| + |ε|) := fun t ht =>
    ⟨by linarith [ht.1, neg_abs_le c, le_abs_self ε], by linarith [ht.2, le_abs_self c, le_abs_self ε]⟩
  have hX0re : ((XiC 0).re : ℂ) = XiC 0 := by
    have h := XiC_ofReal 0
    rw [Complex.ofReal_zero] at h
    rw [h, Complex.ofReal_re]
  refine ⟨fun n => C (XiC 0).re * p n, fun n => (Polynomial.Splits.C _).mul (hsplit n), ?_⟩
  have hmul := (hconv.mono hsub)
  rw [Metric.tendstoUniformlyOn_iff] at hmul ⊢
  intro δ hδ
  filter_upwards [hmul (δ / (‖XiC 0‖ + 1)) (by positivity)] with n hn t ht
  have h1 := hn t ht
  have hX0 := XiC_zero_ne
  rw [dist_eq_norm] at h1 ⊢
  have e : polyEvalC (C (XiC 0).re * p n) t = XiC 0 * polyEvalC (p n) t := by
    simp only [polyEvalC, map_mul, aeval_C, Complex.coe_algebraMap, hX0re]
  rw [e, show XiC t = XiC 0 * (XiC t / XiC 0) by field_simp, ← mul_sub, norm_mul]
  calc ‖XiC 0‖ * ‖XiC t / XiC 0 - polyEvalC (p n) t‖ ≤ ‖XiC 0‖ * (δ / (‖XiC 0‖ + 1)) :=
        mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **RH ⟺ real-rooted approximability of `Ξ` on one zero-free window.** For every real interval
`[c − ε, c + ε]` with `ε > 0` on which `Ξ` does not vanish: RH holds iff `Ξ` is a uniform limit on
that interval of real polynomials with only real zeros. -/
theorem riemannHypothesis_iff_exists_realRooted_tendstoUniformlyOn_shifted {c ε : ℝ}
    (hε : 0 < ε) (hne : ∀ s ∈ Icc (c - ε) (c + ε), XiC s ≠ 0) :
    RiemannHypothesis ↔ ∃ p : ℕ → ℝ[X], (∀ n, (p n).Splits) ∧
      TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t) (fun t : ℝ => XiC t) atTop
        (Icc (c - ε) (c + ε)) := by
  constructor
  · intro hRH
    exact exists_realRooted_tendstoUniformlyOn_shifted_of_rh hRH c ε
  · rintro ⟨p, hs, hc⟩
    exact riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_shifted
      (fun n => ⟨fun _ => p n, fun _ => hs n, Metric.tendstoLocallyUniformly_iff.2
        fun δ hδ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => by simpa using hδ⟩⟩)
      hε hne hc

/-! ## Arbitrary windows -/

/-- `Ξ` vanishes nowhere on some subwindow of every real interval of positive length: otherwise it
would vanish on a set accumulating at a real point, hence identically, but `Ξ(0) ≠ 0`. -/
theorem exists_zeroFree_subwindow {c ε : ℝ} (hε : 0 < ε) :
    ∃ c' ε' : ℝ, 0 < ε' ∧ Icc (c' - ε') (c' + ε') ⊆ Icc (c - ε) (c + ε) ∧
      ∀ s ∈ Icc (c' - ε') (c' + ε'), XiC s ≠ 0 := by
  have hpt : ∃ s₀ ∈ Ioo (c - ε) (c + ε), XiC s₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hfreq : ∃ᶠ z in 𝓝[≠] (c : ℂ), XiC z = 0 := by
      have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          ((Complex.continuous_ofReal.tendsto c).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
      have hev : ∀ᶠ t : ℝ in 𝓝[≠] c, XiC (t : ℂ) = 0 := by
        have hmem : Ioo (c - ε) (c + ε) ∈ 𝓝 c := Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [nhdsWithin_le_nhds hmem] with t ht
        exact hall t ht
      exact htend.frequently hev.frequently
    have hzero := XiC_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ _) hfreq
    exact XiC_zero_ne (hzero (mem_univ 0))
  obtain ⟨s₀, hs₀, hX⟩ := hpt
  have hcont : Continuous fun t : ℝ => XiC t := by
    have hd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
    exact hd.continuous.comp Complex.continuous_ofReal
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne_fun hcont continuous_const) s₀ hX
  set ε' : ℝ := min (δ / 2) (min ((s₀ - (c - ε)) / 2) (((c + ε) - s₀) / 2)) with hε'
  have h1 : 0 < s₀ - (c - ε) := by linarith [hs₀.1]
  have h2 : 0 < (c + ε) - s₀ := by linarith [hs₀.2]
  have hε'pos : 0 < ε' := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε'δ : ε' ≤ δ / 2 := min_le_left _ _
  have hε'l : ε' ≤ (s₀ - (c - ε)) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε'r : ε' ≤ ((c + ε) - s₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀, ε', hε'pos, fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩, fun t ht => ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- **Real-rooted approximation on any interval forces RH.** No zero-free hypothesis is needed. -/
theorem riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_any {F : ℕ → ℂ → ℂ}
    (hLP : ∀ n, GaloisForLFunctions.HTGeometry.LaguerrePolya (F n)) {c ε : ℝ} (hε : 0 < ε)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => F n t) (fun t : ℝ => XiC t) atTop
      (Icc (c - ε) (c + ε))) :
    RiemannHypothesis := by
  obtain ⟨c', ε', hε', hsub, hne⟩ := exists_zeroFree_subwindow (c := c) hε
  exact riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_shifted hLP hε' hne (hconv.mono hsub)

/-- **RH ⟺ real-rooted approximability of `Ξ` on any real interval of positive length.** -/
theorem riemannHypothesis_iff_exists_realRooted_tendstoUniformlyOn_any {c ε : ℝ} (hε : 0 < ε) :
    RiemannHypothesis ↔ ∃ p : ℕ → ℝ[X], (∀ n, (p n).Splits) ∧
      TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (p n) t) (fun t : ℝ => XiC t) atTop
        (Icc (c - ε) (c + ε)) := by
  constructor
  · intro hRH
    exact exists_realRooted_tendstoUniformlyOn_shifted_of_rh hRH c ε
  · rintro ⟨p, hs, hc⟩
    exact riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_any
      (fun n => ⟨fun _ => p n, fun _ => hs n, Metric.tendstoLocallyUniformly_iff.2
        fun δ hδ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => by simpa using hδ⟩⟩)
      hε hc

end

end RHTower.IntervalLaguerrePolya
