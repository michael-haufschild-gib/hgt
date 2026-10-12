import GaloisForLFunctions.RHTower.XiGaussianHeatSpectralDictionary
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Heat Hankel windows are super-exponentially ill-conditioned

The test `f_L = Φ_{≤L−1/4} ⋆ κ₂` has Weil energy at most `C e^{12L} e^{−π e^{2L−1/2}} ‖f_L‖²`.
It is even, so its real and imaginary parts are even real tests carrying the same total energy
and mass. One of them has energy-to-mass ratio below the margin. Mollifying it yields a smooth
even pole-vanishing source of half-width just above `L`.
The spectral dictionary transports its Rayleigh quotient to the pole hyperplane of every heat
window `K > L²/4`. Hence the ground Rayleigh quotient of the window `K` is eventually at most
`C e^{12L} e^{−π e^{2L−1/2}} + ε` for every `L < 2√K`: positivity of a window, when it holds,
holds with a doubly-exponentially small margin.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-! ## The radical test is even -/

theorem riemannPhiCore_neg (L x : ℝ) : riemannPhiCore L (-x) = riemannPhiCore L x := by
  unfold riemannPhiCore
  by_cases h : x ∈ Icc (-(L - 1 / 4)) (L - 1 / 4)
  · have h' : -x ∈ Icc (-(L - 1 / 4)) (L - 1 / 4) := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_mem h', indicator_of_mem h, riemannPhiKernel_neg]
  · have h' : -x ∉ Icc (-(L - 1 / 4)) (L - 1 / 4) := fun hm =>
      h ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [indicator_of_notMem h', indicator_of_notMem h]

theorem deriv_neg_of_even_complex {g : ℝ → ℂ} (hg : ∀ x, g (-x) = g x) (x : ℝ) :
    deriv g (-x) = -deriv g x := by
  have e : g = fun y => g (-y) := funext fun y => (hg y).symm
  have h := deriv_comp_neg (f := g) (x := x)
  rw [← e] at h
  rw [h, neg_neg]

theorem deriv_neg_of_odd_complex {h : ℝ → ℂ} (hh : ∀ x, h (-x) = -h x) (x : ℝ) :
    deriv h (-x) = deriv h x := by
  have e : h = fun y => -h (-y) := funext fun y => by rw [hh, neg_neg]
  have h1 : deriv (fun y => -h (-y)) x = -deriv (fun y => h (-y)) x := deriv.neg
  rw [deriv_comp_neg, ← e] at h1
  rw [h1, neg_neg]

theorem weilBumpC_neg (u : ℝ) : weilBumpC (-u) = weilBumpC u := by
  simp only [weilBumpC, weilBump.neg]

theorem weilBumpPolarFree_neg (u : ℝ) : weilBumpPolarFree (-u) = weilBumpPolarFree u := by
  unfold weilBumpPolarFree
  rw [deriv_neg_of_odd_complex (deriv_neg_of_even_complex weilBumpC_neg), weilBumpC_neg]

theorem weilRadicalTest_neg (L x : ℝ) : weilRadicalTest L (-x) = weilRadicalTest L x := by
  simp only [weilRadicalTest, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_neg_eq_self]
  congr 1
  funext t
  rw [riemannPhiCore_neg, show -x - -t = -(x - t) by ring, weilBumpPolarFree_neg]

/-! ## The margin of the radical test -/

/-- The radical test itself realises the super-exponential Weil margin. -/
theorem zeta_weil_margin_weilRadicalTest :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      0 < ∫ x : ℝ, ‖weilRadicalTest L x‖ ^ 2 ∧
      ‖zetaZeroConfig.W (weilRadicalTest L) (weilRadicalTest L)‖ ≤
        C * Real.exp (12 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) *
          ∫ x : ℝ, ‖weilRadicalTest L x‖ ^ 2 := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; exact tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : ℝ, γ₂ = ‖riemannPhiTransform 2‖ := ⟨_, rfl⟩
  have hγ₂0 : 0 < γ₂ := by rw [hγ₂]; exact norm_pos_iff.mpr riemannPhiTransform_two_ne_zero
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = γ₂ / 2 * (Real.exp (-(3 / 16)) / 2) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have hX0 : 0 ≤ 2 * E₀ * C₆ / γ₂ := by positivity
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = 1 + Real.log (2 * E₀ * C₆ / γ₂ + 1) := ⟨_, rfl⟩
  have hlog0 : 0 ≤ Real.log (2 * E₀ * C₆ / γ₂ + 1) := Real.log_nonneg (by linarith)
  refine ⟨5 / 2 * S * A * K₀ * E₀ / c₁ ^ 2 + 1, L₀, by positivity, by rw [hL₀]; linarith,
    fun L hL => ?_⟩
  have hL1 : 1 ≤ L := by rw [hL₀] at hL; linarith
  have hLpos : 0 < L := by linarith
  -- smallness of the tail at the evaluation point
  have hexpL : 2 * E₀ * C₆ / γ₂ + 1 ≤ Real.exp (L - 1 / 4) := by
    have hle : Real.log (2 * E₀ * C₆ / γ₂ + 1) ≤ L - 1 / 4 := by rw [hL₀] at hL; linarith
    calc 2 * E₀ * C₆ / γ₂ + 1 = Real.exp (Real.log (2 * E₀ * C₆ / γ₂ + 1)) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (L - 1 / 4) := Real.exp_le_exp.mpr hle
  have htail_small : E₀ * C₆ * Real.exp (-(L - 1 / 4)) ≤ γ₂ / 2 := by
    have he := Real.exp_pos (L - 1 / 4)
    have hinv : Real.exp (-(L - 1 / 4)) * Real.exp (L - 1 / 4) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : 2 * E₀ * C₆ ≤ γ₂ * Real.exp (L - 1 / 4) := by
      have := mul_le_mul_of_nonneg_left hexpL hγ₂0.le
      rw [mul_add, mul_div_cancel₀ _ hγ₂0.ne'] at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(L - 1 / 4))).le]
  have hsmall := (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hL1 (b := 3 / 2) le_rfl).trans
    htail_small
  rw [hγ₂] at hsmall
  have hmass := weilRadicalTest_mass_ge hsmall
  rw [← hγ₂, ← hc₁] at hmass
  have hcs := sq_integral_norm_le_of_abs_support (f := weilRadicalTest L) (contDiff_weilRadicalTest L).continuous
    hLpos (fun x hx => weilRadicalTest_eq_zero hx)
  have hW := norm_W_weilRadicalTest_le hK₀ hK (L := L) hLpos.le
  rw [← hS, ← hA] at hW
  have hε : ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) ≤
      E₀ * Real.exp (6 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) := by
    have h1 := integral_norm_riemannPhiTail_mul_exp_le (b := 1 / 2) hL1 (by norm_num)
    rw [← hE₀] at h1
    refine h1.trans ?_
    rw [show 2 * (L - 1 / 4) = 2 * L - 1 / 2 by ring]
    have : Real.exp (6 * (L - 1 / 4)) ≤ Real.exp (6 * L) := Real.exp_le_exp.mpr (by linarith)
    gcongr
  have := weilMargin_arith hL1 hS0 hA0 hK₀ hE0 (Real.exp_pos _).le hc₁0 hW hε hmass hcs
  exact this

/-! ## Selecting a real part with small Weil ratio -/

theorem W_zero_fun : zetaZeroConfig.W (fun _ : ℝ => (0 : ℂ)) (fun _ : ℝ => (0 : ℂ)) = 0 := by
  have h : paperFT (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext z; simp [paperFT]
  simp [ZeroConfig.W, ZeroConfig.Wsummand, h]

theorem re_W_ofReal_eq_zero_of_integral_sq {g : ℝ → ℝ} (hg : Continuous g)
    (hcpt : HasCompactSupport g) (h : ¬ 0 < ∫ x, g x ^ 2) :
    (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re = 0 := by
  have hz : ∀ x, g x = 0 := by
    intro x
    by_contra hx
    apply h
    have h2 : HasCompactSupport (fun x => g x ^ 2) := by
      simpa [Function.comp_def] using hcpt.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    exact (hg.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero h2
      (fun y => sq_nonneg (g y)) (pow_ne_zero 2 hx)
  have e : (fun x => (g x : ℂ)) = fun _ => (0 : ℂ) := funext fun x => by rw [hz x, ofReal_zero]
  rw [e, W_zero_fun, Complex.zero_re]

theorem integrable_sq_of_continuous_compact {g : ℝ → ℝ} (hg : Continuous g)
    (hk : HasCompactSupport g) : Integrable (fun x => g x ^ 2) := by
  have h2 : HasCompactSupport (fun x => g x ^ 2) := by
    simpa [Function.comp_def] using hk.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact (hg.pow 2).integrable_of_hasCompactSupport h2

theorem part_select_arith {N₁ N₂ R₁ R₂ M : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hpos : 0 < N₁ + N₂) (hsum : R₁ + R₂ ≤ M * (N₁ + N₂)) (hz₁ : ¬ 0 < N₁ → R₁ = 0)
    (hz₂ : ¬ 0 < N₂ → R₂ = 0) : (0 < N₁ ∧ R₁ ≤ M * N₁) ∨ (0 < N₂ ∧ R₂ ≤ M * N₂) := by
  by_contra hc
  rw [not_or, not_and_or, not_and_or] at hc
  obtain ⟨c₁, c₂⟩ := hc
  have hM : M * (N₁ + N₂) = M * N₁ + M * N₂ := by ring
  rcases c₁ with c₁ | c₁ <;> rcases c₂ with c₂ | c₂
  · have : N₁ = 0 := le_antisymm (not_lt.1 c₁) hN₁
    have : N₂ = 0 := le_antisymm (not_lt.1 c₂) hN₂
    linarith
  · have e₁ := hz₁ c₁
    have h0 : M * N₁ = 0 := by rw [le_antisymm (not_lt.1 c₁) hN₁, mul_zero]
    linarith [not_le.1 c₂]
  · have e₂ := hz₂ c₂
    have h0 : M * N₂ = 0 := by rw [le_antisymm (not_lt.1 c₂) hN₂, mul_zero]
    linarith [not_le.1 c₁]
  · linarith [not_le.1 c₁, not_le.1 c₂]

/-- An even test whose Weil energy is at most `M` times its mass has an even real or imaginary
part with the same property and positive mass. -/
theorem exists_part_re_W_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hcpt : HasCompactSupport f)
    (heven : ∀ x, f (-x) = f x) {M : ℝ} (hmass : 0 < ∫ x, ‖f x‖ ^ 2)
    (hW : ‖zetaZeroConfig.W f f‖ ≤ M * ∫ x, ‖f x‖ ^ 2) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ (∀ x, g (-x) = g x) ∧ (∀ x, f x = 0 → g x = 0) ∧
      ((∀ x, g x = (f x).re) ∨ (∀ x, g x = (f x).im)) ∧ 0 < ∫ x, g x ^ 2 ∧
      (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re ≤ M * ∫ x, g x ^ 2 := by
  have hc₁ : ContDiff ℝ 2 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hc₂ : ContDiff ℝ 2 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hk₁ : HasCompactSupport (fun x => (f x).re) :=
    hcpt.comp_left (g := Complex.re) Complex.zero_re
  have hk₂ : HasCompactSupport (fun x => (f x).im) :=
    hcpt.comp_left (g := Complex.im) Complex.zero_im
  have hi₁ := integrable_sq_of_continuous_compact hc₁.continuous hk₁
  have hi₂ := integrable_sq_of_continuous_compact hc₂.continuous hk₂
  have hmass_eq : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add hi₁ hi₂]
    congr 1
    funext x
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hre : (zetaZeroConfig.W f f).re ≤ M * ∫ x, ‖f x‖ ^ 2 := (Complex.re_le_norm _).trans hW
  rw [W_eq_re_add_im hf hcpt heven, Complex.add_re, hmass_eq] at hre
  rw [hmass_eq] at hmass
  rcases part_select_arith (integral_nonneg fun _ => sq_nonneg _)
      (integral_nonneg fun _ => sq_nonneg _) hmass hre
      (re_W_ofReal_eq_zero_of_integral_sq hc₁.continuous hk₁)
      (re_W_ofReal_eq_zero_of_integral_sq hc₂.continuous hk₂) with h | h
  · exact ⟨fun x => (f x).re, hc₁, fun x => by simp only [heven], fun x hx => by simp [hx],
      Or.inl fun _ => rfl, h.1, h.2⟩
  · exact ⟨fun x => (f x).im, hc₂, fun x => by simp only [heven], fun x hx => by simp [hx],
      Or.inr fun _ => rfl, h.1, h.2⟩

/-! ## Real mollification -/

/-- The mollification of a real function, as a real function. -/
def realMollify {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (mollify hr (fun y => (g y : ℂ)) x).re

theorem mollify_ofReal_eq {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) (x : ℝ) :
    mollify hr (fun y => (g y : ℂ)) x = ((realMollify hr g x : ℝ) : ℂ) := by
  have h : mollify hr (fun y => (g y : ℂ)) x =
      ((∫ t, (evenBump hr).normed volume t * g (x - t) : ℝ) : ℂ) := by
    rw [mollify_apply, ← integral_complex_ofReal]
    congr 1
    funext t
    simp [bumpC]
  rw [realMollify, h, Complex.ofReal_re]

theorem ofReal_realMollify {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    (fun x => ((realMollify hr g x : ℝ) : ℂ)) = mollify hr (fun y => (g y : ℂ)) :=
  funext fun x => (mollify_ofReal_eq hr g x).symm

theorem contDiff_realMollify {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ (⊤ : ℕ∞) (realMollify hr g) :=
  Complex.reCLM.contDiff.comp (contDiff_mollify hr (Complex.continuous_ofReal.comp hg))

theorem realMollify_neg {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (x : ℝ) :
    realMollify hr g (-x) = realMollify hr g x := by
  simp only [realMollify]
  rw [mollify_neg hr (fun y => by simp only [heven])]

theorem tsupport_ofReal_subset {g : ℝ → ℝ} {a : ℝ} (hsupp : ∀ x, a < |x| → g x = 0) :
    tsupport (fun y => (g y : ℂ)) ⊆ Icc (-a) a := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  apply hx
  have h : a < |x| := by
    rw [Set.mem_Icc, not_and_or] at hc
    rcases hc with h | h
    · push Not at h; exact lt_abs.2 (Or.inr (by linarith))
    · push Not at h; exact lt_abs.2 (Or.inl h)
  simp [hsupp x h]

theorem realMollify_eq_zero {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} {a : ℝ}
    (hsupp : ∀ x, a < |x| → g x = 0) {x : ℝ} (hx : a + r < |x|) : realMollify hr g x = 0 := by
  simp only [realMollify]
  rw [mollify_eq_zero hr (tsupport_ofReal_subset hsupp) hx, Complex.zero_re]

theorem mollify_eq_lsmul {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) :
    mollify hr f =
      MeasureTheory.convolution ((evenBump hr).normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ)
        volume := by
  funext x
  simp only [mollify, convolution_def, bumpC, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, Complex.real_smul]

theorem tendsto_realMollify {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    Tendsto (fun k : ℕ => realMollify (invSucc_pos k) g x) atTop (𝓝 (g x)) := by
  have hr : Tendsto (fun k : ℕ => (evenBump (invSucc_pos k)).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hr
    (Complex.continuous_ofReal.comp hg) x
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, Complex.ofReal_re] at h2
  refine h2.congr fun k => ?_
  simp only [realMollify]
  rw [mollify_eq_lsmul]

theorem abs_realMollify_le {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} {B : ℝ} (hB : ∀ y, |g y| ≤ B)
    (x : ℝ) : |realMollify hr g x| ≤ B := by
  have hint : Integrable (fun t => (evenBump hr).normed volume t * B) :=
    (evenBump hr).integrable_normed.mul_const B
  have h1 : ‖mollify hr (fun y => (g y : ℂ)) x‖ ≤ ∫ t, (evenBump hr).normed volume t * B := by
    rw [mollify_apply]
    refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun t => ?_)
    simp only [bumpC, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ((evenBump hr).nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hB _) ((evenBump hr).nonneg_normed t)
  rw [integral_mul_const, (evenBump hr).integral_normed, one_mul] at h1
  exact (Complex.abs_re_le_norm _).trans h1

/-- **Mollification converges in `L²`.** -/
theorem tendsto_integral_sq_realMollify {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ}
    (hsupp : ∀ x, a < |x| → g x = 0) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    Tendsto (fun k : ℕ => ∫ x, realMollify (invSucc_pos k) g x ^ 2) atTop
      (𝓝 (∫ x, g x ^ 2)) := by
  have hDi : Integrable ((Icc (-(a + 1)) (a + 1)).indicator (fun _ => B ^ 2)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hDi (fun k => ?_)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((contDiff_realMollify (invSucc_pos k) hg).continuous.pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ Icc (-(a + 1)) (a + 1)
    · rw [Set.indicator_of_mem hx, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_realMollify_le _ hB x) 2
    · rw [Set.indicator_of_notMem hx]
      have hxa : a + 1 < |x| := by
        rw [Set.mem_Icc, not_and_or] at hx
        rcases hx with h | h
        · push Not at h; exact lt_abs.2 (Or.inr (by linarith))
        · push Not at h; exact lt_abs.2 (Or.inl h)
      have hr1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      rw [realMollify_eq_zero _ hsupp (by linarith), sq, mul_zero]
  · exact (tendsto_realMollify hg x).pow 2

/-! ## A smooth source with small Rayleigh quotient -/

theorem tsupport_subset_Icc_of_abs {u : ℝ → ℝ} {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) :
    tsupport u ⊆ Icc (-A) A := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  apply hx
  rw [Set.mem_Icc, not_and_or] at hc
  rcases hc with h | h
  · push Not at h; exact hsupp x (lt_abs.2 (Or.inr (by linarith)))
  · push Not at h; exact hsupp x (lt_abs.2 (Or.inl h))

theorem hasCompactSupport_of_abs_le {u : ℝ → ℝ} {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) :
    HasCompactSupport u :=
  IsCompact.of_isClosed_subset (isCompact_Icc (a := -A) (b := A)) (isClosed_tsupport _)
    (tsupport_subset_Icc_of_abs hsupp)

/-- **Smoothing a real even test keeps its Weil ratio.** -/
theorem exists_smooth_source_ratio_lt {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (heven : ∀ x, g (-x) = g x) {L : ℝ} (hsupp : ∀ x, L < |x| → g x = 0)
    (hpole : ∫ x, g x * Real.exp (-(x / 2)) = 0) (hN : 0 < ∫ x, g x ^ 2) {M : ℝ}
    (hR : (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re ≤ M * ∫ x, g x ^ 2)
    {A : ℝ} (hLA : L < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ t : ℝ, A < |t| → u t = 0) ∧
      (∀ x, u (-x) = u x) ∧ ∫ x, u x * Real.exp (x / 2) = 0 ∧ 0 < ∫ x, u x ^ 2 ∧
      (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
        (xiSpectralPoint q) ^ 2).re / (∫ x, u x ^ 2) < M + ε := by
  have hgc := hg.continuous
  have hgk : HasCompactSupport g := hasCompactSupport_of_abs_le hsupp
  have hfc : Continuous (fun y => (g y : ℂ)) := Complex.continuous_ofReal.comp hgc
  have hfk : HasCompactSupport (fun y => (g y : ℂ)) :=
    hgk.comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero
  have hf2 : ContDiff ℝ 2 (fun y => (g y : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  obtain ⟨B, hB⟩ := hgk.exists_bound_of_continuous hgc
  have hB' : ∀ y, |g y| ≤ B := fun y => by rw [← Real.norm_eq_abs]; exact hB y
  -- limits
  have hNlim := tendsto_integral_sq_realMollify hgc hsupp hB'
  have hWlim : Tendsto (fun k : ℕ => (zetaZeroConfig.W
      (fun x => ((realMollify (invSucc_pos k) g x : ℝ) : ℂ))
      (fun x => ((realMollify (invSucc_pos k) g x : ℝ) : ℂ))).re) atTop
      (𝓝 (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_W_mollify hf2 hfk)
    refine h.congr fun k => ?_
    simp only [Function.comp_def, ofReal_realMollify]
  have hratio := hWlim.div hNlim hN.ne'
  have hRN : (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re /
      (∫ x, g x ^ 2) < M + ε := by
    rw [div_lt_iff₀ hN]; nlinarith
  have hrad : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hrad.eventually (gt_mem_nhds (sub_pos.2 hLA))).and
    ((hNlim.eventually (lt_mem_nhds hN)).and (hratio.eventually (gt_mem_nhds hRN)))).exists
  set r := 1 / ((k : ℝ) + 1) with hr
  have hr0 : 0 < r := invSucc_pos k
  set u := realMollify (invSucc_pos k) g with hu
  have hsuppu : ∀ t : ℝ, A < |t| → u t = 0 := fun t ht =>
    realMollify_eq_zero _ hsupp (by linarith)
  have heu : ∀ x, u (-x) = u x := realMollify_neg _ heven
  have hsm : ContDiff ℝ (⊤ : ℕ∞) u := contDiff_realMollify _ hgc
  have hku : HasCompactSupport u := hasCompactSupport_of_abs_le hsuppu
  -- the pole
  have hpg : paperFT (fun y => (g y : ℂ)) (I / 2) = 0 := by
    rw [paperFT_ofReal_I_half_eq_integral, hpole, Complex.ofReal_zero]
  have hpu : paperFT (fun x => (u x : ℂ)) (I / 2) = 0 := by
    rw [hu, ofReal_realMollify, paperFT_mollify _ hfc hfk, hpg, mul_zero]
  have hpu' : ∫ x, u x * Real.exp (x / 2) = 0 := by
    rw [paperFT_ofReal_I_half_eq_integral] at hpu
    rw [integral_mul_exp_half_of_even heu]
    exact_mod_cast hpu
  -- the support for the bridge
  have hIcc := tsupport_subset_Icc_of_abs hsuppu
  have hts : tsupport u ⊆ Ioo (-(|A| + 1)) (|A| + 1) := fun x hx => by
    have h := hIcc hx
    exact ⟨by linarith [h.1, le_abs_self A], by linarith [h.2, le_abs_self A]⟩
  refine ⟨u, hsm, hku, hsuppu, heu, hpu', hk2, ?_⟩
  rw [← re_W_ofReal_eq_tsum_sq hsm hku heu (by positivity) hts]
  exact hk3

/-! ## The conditioning law -/

/-- The real and imaginary parts of a pole-vanishing test are pole-vanishing. -/
theorem integral_part_mul_exp_eq_zero {f : ℝ → ℂ} (hf : Continuous f) (hcpt : HasCompactSupport f)
    (hp : paperFT f (I / 2) = 0) :
    ∫ x, (f x).re * Real.exp (-(x / 2)) = 0 ∧ ∫ x, (f x).im * Real.exp (-(x / 2)) = 0 := by
  have hsplit := paperFT_eq_re_add_im hf hcpt (I / 2)
  rw [hp, paperFT_ofReal_I_half_eq_integral (fun x => (f x).re),
    paperFT_ofReal_I_half_eq_integral (fun x => (f x).im)] at hsplit
  constructor
  · have := congrArg Complex.re hsplit
    simpa using this.symm
  · have := congrArg Complex.im hsplit
    simpa using this.symm

/-- **Heat windows are super-exponentially ill-conditioned.**  There are `C > 0` and `L₀` such
that for every `L ≥ L₀`, every window `K > L²/4` and every `ε > 0`, the pole hyperplane at heat
time `K/n` eventually contains a polynomial whose heat Hankel energy is at most
`(C e^{12L} e^{−π e^{2L−1/2}} + ε)` times the `L²` mass of its physical heat test. -/
theorem eventually_exists_poleHyperplane_rayleigh_lt_weilMargin :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ K : ℝ, L ^ 2 < 4 * K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
        0 < ∫ x, heatTest (K / n) P x ^ 2 ∧
        (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re <
          (C * Real.exp (12 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) + ε) *
            ∫ x, heatTest (K / n) P x ^ 2 := by
  obtain ⟨C, L₀, hC, hL₀, hmar⟩ := zeta_weil_margin_weilRadicalTest
  refine ⟨C, L₀, hC, hL₀, fun L hL K hLK ε hε => ?_⟩
  have hL1 : 1 ≤ L := hL₀.trans hL
  obtain ⟨hmass, hW⟩ := hmar L hL
  have hf := contDiff_weilRadicalTest L
  have hcpt : HasCompactSupport (weilRadicalTest L) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_weilRadicalTest L)
  obtain ⟨g, hg2, hge, hgz, hgform, hgN, hgR⟩ :=
    exists_part_re_W_le hf hcpt (weilRadicalTest_neg L) hmass hW
  have hsg : ∀ x, L < |x| → g x = 0 := fun x hx => hgz x (weilRadicalTest_eq_zero hx)
  obtain ⟨hre0, him0⟩ := integral_part_mul_exp_eq_zero hf.continuous hcpt
    (paperFT_weilRadicalTest_half_I L)
  have hpg : ∫ x, g x * Real.exp (-(x / 2)) = 0 := by
    rcases hgform with h | h
    · rw [← hre0]; congr 1; funext x; rw [h x]
    · rw [← him0]; congr 1; funext x; rw [h x]
  have hK0 : 0 < K := by nlinarith
  have hs := Real.sqrt_pos.2 hK0
  have hs2 := Real.sq_sqrt hK0.le
  have hL2 : L < 2 * Real.sqrt K := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by positivity) h 2
    rw [mul_pow, hs2] at this
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (L + 2 * Real.sqrt K) / 2 := ⟨_, rfl⟩
  have hLA : L < A := by rw [hA]; linarith
  have hA2 : A < 2 * Real.sqrt K := by rw [hA]; linarith
  have hAK : A ^ 2 < 4 * K := by
    have := pow_lt_pow_left₀ hA2 (by rw [hA]; positivity) two_ne_zero
    rw [mul_pow, hs2] at this
    linarith
  obtain ⟨u, hu, hcu, hsu, heu, hpu, hNu, hratio⟩ :=
    exists_smooth_source_ratio_lt hg2 hge hsg hpg hgN hgR hLA (half_pos hε)
  filter_upwards [eventually_exists_poleHyperplane_rayleigh_lt hu hcu hsu heu hpu hK0 hAK hNu
    (half_pos hε)] with n hn
  obtain ⟨P, hPd, hPe, hG, hlt⟩ := hn
  refine ⟨P, hPd, hPe, hG, hlt.trans_le (mul_le_mul_of_nonneg_right ?_ hG.le)⟩
  linarith

/-- **The conditioning law in window form.**  For every large window `K` and every `ε > 0`, the
ground Rayleigh quotient of the heat Hankel form on the pole hyperplane at heat time `K/n` is
eventually below `C e^{24√K} e^{−π e^{4√K−1}} + ε`. -/
theorem eventually_exists_poleHyperplane_rayleigh_lt_doubleExp :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
        0 < ∫ x, heatTest (K / n) P x ^ 2 ∧
        (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re <
          (C * Real.exp (24 * Real.sqrt K) * Real.exp (-π * Real.exp (4 * Real.sqrt K - 1)) +
            ε) * ∫ x, heatTest (K / n) P x ^ 2 := by
  obtain ⟨C, L₀, hC, hL₀, hlaw⟩ := eventually_exists_poleHyperplane_rayleigh_lt_weilMargin
  refine ⟨C, ((L₀ + 1 / 4) / 2) ^ 2, hC, by positivity, fun K hK ε hε => ?_⟩
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hs := Real.sqrt_nonneg K
  have hs2 := Real.sq_sqrt hK0.le
  have hsK : (L₀ + 1 / 4) / 2 ≤ Real.sqrt K := by
    rw [← Real.sqrt_sq (show 0 ≤ (L₀ + 1 / 4) / 2 by positivity)]
    exact Real.sqrt_le_sqrt hK
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.sqrt K - 1 / 4 := ⟨_, rfl⟩
  have hLL₀ : L₀ ≤ L := by rw [hL]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hLK : L ^ 2 < 4 * K := by
    have h1 : L < 2 * Real.sqrt K := by rw [hL]; linarith
    have := pow_lt_pow_left₀ h1 hL0 two_ne_zero
    rw [mul_pow, hs2] at this
    linarith
  filter_upwards [hlaw L hLL₀ K hLK ε hε] with n hn
  obtain ⟨P, hPd, hPe, hG, hlt⟩ := hn
  refine ⟨P, hPd, hPe, hG, hlt.trans_le (mul_le_mul_of_nonneg_right ?_ hG.le)⟩
  have e1 : Real.exp (12 * L) ≤ Real.exp (24 * Real.sqrt K) :=
    Real.exp_le_exp.2 (by rw [hL]; linarith)
  have e2 : 2 * L - 1 / 2 = 4 * Real.sqrt K - 1 := by rw [hL]; ring
  rw [e2]
  have hpos := (Real.exp_pos (-π * Real.exp (4 * Real.sqrt K - 1))).le
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC.le) hpos
  linarith

end

end RHTower
