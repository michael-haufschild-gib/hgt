import GaloisForLFunctions.RHTower.WeightedEulerStripFourierContourShift
import Mathlib.Analysis.Fourier.Inversion

/-!
# Paley–Wiener vanishing for two-ray decaying entire functions

An entire function of exponential type `τ` that decays like `e^{-ε|x|}` on
both real rays vanishes identically.  This is the vanishing form of the
indicator inequality `h(0) + h(π) ≥ 0` for entire functions of exponential
type.

The proof chains the strip machinery: the global bound
`‖g z‖ ≤ K e^{-ε|Re z| + τ|Im z|}` makes the Fourier transform
`Φ(w) = ∫ g(x)e^{-iwx}dx` analytic on the strip `|Im w| < ε`; the contour
shift kills `Φ` at real frequencies `|w| > τ`; the identity theorem on the
connected strip then forces `Φ ≡ 0`; Fourier inversion recovers `g|_ℝ = 0`,
and the identity theorem on `ℂ` finishes.

The capstone `eq_zero_of_two_ray_exponential_decay` packages the statement
directly from the exponential-type growth and two-ray decay hypotheses.
Everything is unconditional.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter Topology

variable {g : ℂ → ℂ} {K ε τ : ℝ}

/-- The open horizontal strip is convex. -/
theorem convex_absIm_strip (ε : ℝ) : Convex ℝ {w : ℂ | |w.im| < ε} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp [Complex.add_im]
  calc |(a • x + b • y).im| = |a * x.im + b * y.im| := by rw [him]
    _ ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
    _ = a * |x.im| + b * |y.im| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * max |x.im| |y.im| + b * max |x.im| |y.im| := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |x.im| |y.im| := by rw [← add_mul, hab, one_mul]
    _ < ε := max_lt hx hy

/-- The strip Fourier transform of a two-ray-bounded entire function vanishes
on the whole strip: the high frequencies vanish by contour shift, and the
identity theorem propagates the zero set. -/
theorem stripFourier_eqOn_zero (hg : Differentiable ℂ g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (hτ : 0 ≤ τ) :
    Set.EqOn (stripFourier g) 0 {w : ℂ | |w.im| < ε} := by
  have hA := analyticOnNhd_stripFourier hg hbound
  have hpre : IsPreconnected {w : ℂ | |w.im| < ε} :=
    (convex_absIm_strip ε).isPreconnected
  have hz₀ : (((τ + 1 : ℝ)) : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simpa using hε
  -- the zero frequencies accumulate at `τ + 1`
  have hseqR : Tendsto (fun n : ℕ => (τ + 1 + 1 / (n + 1) : ℝ)) atTop
      (𝓝 (τ + 1)) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.const_add (τ + 1 : ℝ)
  have hseq : Tendsto (fun n : ℕ => (((τ + 1 + 1 / (n + 1) : ℝ)) : ℂ)) atTop
      (𝓝[≠] (((τ + 1 : ℝ)) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_ofReal.tendsto _).comp hseqR
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      rw [Complex.ofReal_inj] at hcontra
      have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
      linarith
  have hvals : ∀ᶠ n : ℕ in atTop,
      stripFourier g (((τ + 1 + 1 / (n + 1) : ℝ)) : ℂ) = 0 := by
    filter_upwards with n
    apply stripFourier_eq_zero_of_abs_gt hg hbound hε hτ
    have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
    rw [abs_of_pos (by linarith : (0:ℝ) < τ + 1 + 1 / (n + 1))]
    linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (((τ + 1 : ℝ)) : ℂ), stripFourier g z = 0 :=
    hseq.frequently hvals.frequently
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hz₀ hfreq

/-- A two-ray-bounded entire function vanishes on the real axis, by Fourier
inversion against the vanishing strip transform. -/
theorem eq_zero_on_real_of_strip_bound (hg : Differentiable ℂ g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (hτ : 0 ≤ τ) :
    ∀ x : ℝ, g x = 0 := by
  have hEq := stripFourier_eqOn_zero hg hbound hε hτ
  set gr : ℝ → ℂ := fun x : ℝ => g x with hgr
  have hgrc : Continuous gr := hg.continuous.comp Complex.continuous_ofReal
  have hint : Integrable gr := by
    have h := integrable_stripFourier_kernel hg.continuous hbound
      (w := (0:ℂ)) (by simpa using hε)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [hgr]
  have hFzero : FourierTransform.fourier gr = 0 := by
    funext ξ
    have hbridge : FourierTransform.fourier gr ξ
        = stripFourier g (((2 * Real.pi * ξ : ℝ)) : ℂ) := by
      rw [Real.fourier_eq']
      unfold stripFourier
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [RCLike.inner_apply, conj_trivial, hgr]
      rw [smul_eq_mul, mul_comm]
      congr 1
      push_cast
      ring
    rw [hbridge]
    have hmem : (((2 * Real.pi * ξ : ℝ)) : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
      simpa using hε
    simpa using hEq hmem
  have hFint : Integrable (FourierTransform.fourier gr) := by
    rw [hFzero]
    exact integrable_zero _ _ _
  have hinv := hgrc.fourierInv_fourier_eq hint hFint
  rw [hFzero] at hinv
  have hzero : FourierTransformInv.fourierInv (0 : ℝ → ℂ) = 0 := by
    funext w
    rw [Real.fourierInv_eq]
    simp
  rw [hzero] at hinv
  intro x
  exact congrFun hinv.symm x

/-- **Vanishing under a strip bound**: an entire function satisfying the
two-ray strip bound is identically zero. -/
theorem eq_zero_of_strip_bound (hg : Differentiable ℂ g)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ K * Real.exp (-(ε * |z.re|) + τ * |z.im|))
    (hε : 0 < ε) (hτ : 0 ≤ τ) :
    g = 0 := by
  have hreal := eq_zero_on_real_of_strip_bound hg hbound hε hτ
  have hAnal : AnalyticOnNhd ℂ g Set.univ :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hseq : Tendsto (fun n : ℕ => (((1 / (n + 1) : ℝ)) : ℂ)) atTop
      (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp h0
      rw [show ((0:ℂ)) = ((0:ℝ):ℂ) from by norm_num]
      exact h1
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      rw [show (0 : ℂ) = ((0:ℝ) : ℂ) from by norm_num, Complex.ofReal_inj]
        at hcontra
      have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 :=
    hseq.frequently (Eventually.of_forall fun n => hreal _).frequently
  have hEq := hAnal.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ 0) hfreq
  funext z
  exact hEq (Set.mem_univ z)

/-- **Paley–Wiener vanishing / two-ray indicator theorem**: an entire
function of exponential type that decays exponentially on both real rays is
identically zero. -/
theorem eq_zero_of_two_ray_exponential_decay
    (hg : Differentiable ℂ g) {A C : ℝ} (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp (τ * ‖z‖))
    (hplus : ∀ x : ℝ, 0 ≤ x → ‖g (x : ℂ)‖ ≤ C * Real.exp (-(ε * x)))
    (hminus : ∀ x : ℝ, x ≤ 0 → ‖g (x : ℂ)‖ ≤ C * Real.exp (ε * x)) :
    g = 0 :=
  eq_zero_of_strip_bound hg
    (norm_le_exp_of_two_ray_exponential_decay hg hA hgrow hplus hminus) hε hτ

end RHTower
