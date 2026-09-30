import GaloisForLFunctions.RHTower.ZetaNotchTwistedOffDiagonal
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth

/-!
# Large twists: the crude tail of the windowed twisted moment

The function `t ↦ |ζ(½+it)|²` is the restriction to `ℝ` of `F(z) = ζ(½+iz) ζ(½−iz)`, which is
holomorphic on the strip `|Im z| < ½`. On the circle of radius `¼` about a height `t ≥ 8` the
one-term Euler–Maclaurin strip bound gives `|F| ≤ 81 t²`, so Cauchy's estimate gives the height jets
`|∂_t^n |ζ(½+it)|²| ≤ n! 4^n · 81 t²` (`norm_iteratedDeriv_zetaSq_le`). Then `K` integrations by parts
against the window give (`exists_norm_twistedMoment_le_pow`)

`‖∫ ω(t) |ζ(½+it)|² e^{−iξt} dt‖ ≤ C_K L³ / |ξ|^K`,

with the power of `L` independent of `K`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-- The holomorphic extension `F(z) = ζ(½ + iz) ζ(½ − iz)` of `|ζ(½+it)|²`. -/
def zetaPairC (z : ℂ) : ℂ :=
  riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + (-z) * I)

theorem zetaPairC_ofReal (t : ℝ) : zetaPairC t = zetaSq t := by
  unfold zetaPairC zetaSq linePt
  rw [Complex.ofReal_neg]

theorem half_add_mul_I_eq (w : ℂ) :
    ((1 / 2 : ℝ) : ℂ) + w * I = ((1 / 2 - w.im : ℝ) : ℂ) + (w.re : ℂ) * I := by
  apply Complex.ext
  · simp
    ring
  · simp

theorem half_add_mul_I_ne_one {w : ℂ} (hw : |w.im| < 1 / 2) : ((1 / 2 : ℝ) : ℂ) + w * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have := abs_lt.mp hw
  linarith

theorem differentiableAt_zetaPairC {z : ℂ} (hz : |z.im| < 1 / 2) :
    DifferentiableAt ℂ zetaPairC z := by
  have h1 := half_add_mul_I_ne_one hz
  have h2 : ((1 / 2 : ℝ) : ℂ) + (-z) * I ≠ 1 :=
    half_add_mul_I_ne_one (by rw [Complex.neg_im, abs_neg]; exact hz)
  unfold zetaPairC
  exact ((differentiableAt_riemannZeta h1).comp z (by fun_prop)).mul
    ((differentiableAt_riemannZeta h2).comp z (by fun_prop))

theorem analyticAt_zetaPairC_ofReal (t : ℝ) : AnalyticAt ℂ zetaPairC (t : ℂ) := by
  have hU : IsOpen {z : ℂ | |z.im| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine DifferentiableOn.analyticAt (s := {z : ℂ | |z.im| < 1 / 2})
    (fun z hz => (differentiableAt_zetaPairC hz).differentiableWithinAt) (hU.mem_nhds ?_)
  simp

theorem contDiff_zetaSq (n : ℕ) : ContDiff ℝ n zetaSq := by
  have h : ∀ u : ℝ, AnalyticAt ℝ zetaSq u := by
    intro u
    have hc : AnalyticAt ℝ (fun t : ℝ => zetaPairC (t : ℂ)) u :=
      (analyticAt_zetaPairC_ofReal u).restrictScalars.comp
        (Complex.ofRealCLM.analyticAt u)
    exact hc.congr (Filter.Eventually.of_forall fun t => zetaPairC_ofReal t)
  exact contDiff_iff_contDiffAt.mpr fun u => (h u).contDiffAt

/-- `‖ζ(½ + iw)‖ ≤ 9t` for `|Im w| ≤ ¼`, `2 ≤ |Re w| ≤ t + ¼`, `t ≥ 4`. -/
theorem norm_riemannZeta_half_add_mul_I_le {w : ℂ} {t : ℝ} (ht : 4 ≤ t) (him : |w.im| ≤ 1 / 4)
    (hre1 : 2 ≤ |w.re|) (hre2 : |w.re| ≤ t + 1 / 4) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + w * I)‖ ≤ 9 * t := by
  rw [half_add_mul_I_eq]
  have hi := abs_le.mp him
  have hσ : 1 / 2 - w.im ∈ Ioc (0 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h := RHTower.ZetaGateProductAFE.norm_riemannZeta_le_strip' hσ hre1
  have hden : |w.re| ≤ ‖1 - (((1 / 2 - w.im : ℝ) : ℂ) + (w.re : ℂ) * I)‖ := by
    have := Complex.abs_im_le_norm (1 - (((1 / 2 - w.im : ℝ) : ℂ) + (w.re : ℂ) * I))
    have him' : (1 - (((1 / 2 - w.im : ℝ) : ℂ) + (w.re : ℂ) * I)).im = -w.re := by simp
    rw [him', abs_neg] at this
    exact this
  have h1 : 1 / ‖1 - (((1 / 2 - w.im : ℝ) : ℂ) + (w.re : ℂ) * I)‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : 2 * |w.re| / (1 / 2 - w.im) ≤ 8 * |w.re| := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg w.re]
  linarith

/-- **Cauchy jets of `|ζ(½+it)|²`**: `‖∂_t^n |ζ(½+it)|²‖ ≤ n! 4^n · 81 t²` for `t ≥ 8`. -/
theorem norm_iteratedDeriv_zetaSq_le (n : ℕ) {t : ℝ} (ht : 8 ≤ t) :
    ‖iteratedDeriv n zetaSq t‖ ≤ n.factorial * 4 ^ n * (81 * t ^ 2) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hid : iteratedDeriv n zetaSq t = iteratedDeriv n zetaPairC (t : ℂ) := by
    have e : zetaSq = fun x : ℝ => zetaPairC (x : ℂ) := funext fun x => (zetaPairC_ofReal x).symm
    rw [e]
    exact HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt (T := 0) n
      (fun s _ => analyticAt_zetaPairC_ofReal s) t ht0
  rw [hid]
  have hdiff : DiffContOnCl ℂ zetaPairC (Metric.ball (t : ℂ) (1 / 4)) := by
    refine DifferentiableOn.diffContOnCl fun z hz => ?_
    rw [closure_ball _ (by norm_num)] at hz
    have hz' : ‖z - t‖ ≤ 1 / 4 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have him : |z.im| ≤ 1 / 4 := by
      have := Complex.abs_im_le_norm (z - t)
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    exact (differentiableAt_zetaPairC (by linarith)).differentiableWithinAt
  have hbound : ∀ z ∈ Metric.sphere (t : ℂ) (1 / 4), ‖zetaPairC z‖ ≤ 81 * t ^ 2 := by
    intro z hz
    have hz' : ‖z - t‖ = 1 / 4 := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have him : |z.im| ≤ 1 / 4 := by
      have := Complex.abs_im_le_norm (z - t)
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    have hre : |z.re - t| ≤ 1 / 4 := by
      have := Complex.abs_re_le_norm (z - t)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hr := abs_le.mp hre
    have hre1 : 2 ≤ |z.re| := by rw [abs_of_pos (by linarith)]; linarith
    have hre2 : |z.re| ≤ t + 1 / 4 := by rw [abs_of_pos (by linarith)]; linarith
    have e1 := norm_riemannZeta_half_add_mul_I_le (w := z) (by linarith) him hre1 hre2
    have e2 := norm_riemannZeta_half_add_mul_I_le (w := -z) (t := t) (by linarith)
      (by rwa [Complex.neg_im, abs_neg]) (by rwa [Complex.neg_re, abs_neg])
      (by rwa [Complex.neg_re, abs_neg])
    unfold zetaPairC
    rw [norm_mul]
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + -z * I)‖
        ≤ (9 * t) * (9 * t) := mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = 81 * t ^ 2 := by ring
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hdiff hbound
  refine h.trans (le_of_eq ?_)
  rw [one_div, inv_pow, div_inv_eq_mul]
  ring

/-! ## The crude tail -/

/-- The windowed `|ζ|²`. -/
def notchZetaSq (L : ℝ) (t : ℝ) : ℂ := notchWindow L t * zetaSq t

theorem contDiff_notchZetaSq (L : ℝ) (n : ℕ) : ContDiff ℝ n (notchZetaSq L) :=
  ((contDiff_notchWindow L).of_le (WithTop.coe_le_coe.mpr le_top)).mul (contDiff_zetaSq n)

theorem notchZetaSq_eq_zero {L t : ℝ} (hL : 0 < L) (ht : t ∉ Icc (L / 2) (5 * L / 2)) :
    notchZetaSq L t = 0 := by
  unfold notchZetaSq
  rw [notchWindow_eq_zero hL ht, zero_mul]

theorem hasCompactSupport_notchZetaSq {L : ℝ} (hL : 0 < L) : HasCompactSupport (notchZetaSq L) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => notchZetaSq_eq_zero hL ht

theorem iteratedDeriv_notchZetaSq_eq_zero (n : ℕ) {L t : ℝ} (hL : 0 < L)
    (ht : t ∉ Icc (L / 2) (5 * L / 2)) : iteratedDeriv n (notchZetaSq L) t = 0 := by
  have hopen : IsOpen (Icc (L / 2) (5 * L / 2))ᶜ := isClosed_Icc.isOpen_compl
  have hev : notchZetaSq L =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact notchZetaSq_eq_zero hL hs
  rw [hev.iteratedDeriv_eq n]
  simp

/-- The crude jet constant. -/
def crudeJetConst (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j) *
    ((K - j).factorial * 4 ^ (K - j) * 507)

theorem crudeJetConst_nonneg (K : ℕ) : 0 ≤ crudeJetConst K :=
  Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg (blockWindowConst_nonneg j) (by positivity))) (by positivity)

theorem norm_iteratedDeriv_notchZetaSq_le (K : ℕ) {L t : ℝ} (hL : 16 ≤ L)
    (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    ‖iteratedDeriv K (notchZetaSq L) t‖ ≤ crudeJetConst K * L ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL2 : (0 : ℝ) < L / 2 := by linarith
  have ht8 : (8 : ℝ) ≤ t := by linarith [ht.1]
  have hleib := norm_iteratedFDeriv_mul_le
    ((contDiff_notchWindow L).of_le (WithTop.coe_le_coe.mpr le_top) :
      ContDiff ℝ ((K : ℕ∞) : WithTop ℕ∞) (notchWindow L))
    (contDiff_zetaSq K) t (le_refl ((K : ℕ∞) : WithTop ℕ∞))
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
  unfold notchZetaSq
  refine hleib.trans ?_
  rw [crudeJetConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_iteratedDeriv_blockWindowC_le j L (2 * L) hL2 t
  have h1' : ‖iteratedDeriv j (notchWindow L) t‖ ≤ blockWindowConst j * 2 ^ j := by
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hc := blockWindowConst_nonneg j
    have hLj : (1 : ℝ) ≤ (L / 2) ^ j := one_le_pow₀ (by linarith)
    have : blockWindowConst j ≤ blockWindowConst j * 2 ^ j := by
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
  have h2 := norm_iteratedDeriv_zetaSq_le (K - j) ht8
  have ht2 : 81 * t ^ 2 ≤ 507 * L ^ 2 := by nlinarith [ht.2]
  have h2' : ‖iteratedDeriv (K - j) zetaSq t‖ ≤ (K - j).factorial * 4 ^ (K - j) * (507 * L ^ 2) :=
    h2.trans (mul_le_mul_of_nonneg_left ht2 (by positivity))
  calc (K.choose j : ℝ) * ‖iteratedDeriv j (notchWindow L) t‖ * ‖iteratedDeriv (K - j) zetaSq t‖
      ≤ (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j) *
          ((K - j).factorial * 4 ^ (K - j) * (507 * L ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1' (by positivity)) h2' (norm_nonneg _)
          (mul_nonneg (by positivity) (mul_nonneg (blockWindowConst_nonneg j) (by positivity)))
    _ = (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j) *
          ((K - j).factorial * 4 ^ (K - j) * 507) * L ^ 2 := by ring

/-- **The crude tail**: `‖∫ ω|ζ|² e^{−iξt}‖ ≤ 2 c_K L³/|ξ|^K` for `ξ ≠ 0`. -/
theorem norm_twistedMoment_le_pow (K : ℕ) {L ξ : ℝ} (hL : 16 ≤ L) (hξ : ξ ≠ 0) :
    ‖twistedMoment L ξ‖ ≤ 2 * crudeJetConst K * L ^ 3 / |ξ| ^ K := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hcd := contDiff_notchZetaSq L K
  have hsupp := hasCompactSupport_notchZetaSq hL0
  have h := norm_integral_mul_cexp_le_of_iteratedDeriv K hcd
    (fun n hn => integrable_iteratedDeriv_of_hasCompactSupport hcd hsupp hn) hξ
  have hI := integral_norm_le_of_forall_mem_Icc (g := iteratedDeriv K (notchZetaSq L))
    (a := L / 2) (b := 5 * L / 2) (M := crudeJetConst K * L ^ 2) (by linarith)
    (integrable_iteratedDeriv_of_hasCompactSupport hcd hsupp le_rfl)
    (fun t ht => iteratedDeriv_notchZetaSq_eq_zero K hL0 ht)
    (fun t ht => norm_iteratedDeriv_notchZetaSq_le K hL ht)
  unfold twistedMoment
  refine h.trans ?_
  have hξ0 : 0 < |ξ| ^ K := pow_pos (abs_pos.mpr hξ) K
  calc (∫ t, ‖iteratedDeriv K (notchZetaSq L) t‖) / |ξ| ^ K
      ≤ ((5 * L / 2 - L / 2) * (crudeJetConst K * L ^ 2)) / |ξ| ^ K :=
        div_le_div_of_nonneg_right hI hξ0.le
    _ = 2 * crudeJetConst K * L ^ 3 / |ξ| ^ K := by ring

end RHTower.ZetaNotch
