import GaloisForLFunctions.RHTower.SuzukiWeilPropThreeOne
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic

/-!
# Suzuki's Proposition 3.1: the determinacy endgame

`SuzukiWeilPropThreeOne` shows that `𝔓_t(z)` and `P_t(z)` have the same Laplace transform in `t`
for every large real `σ`.  This module turns that into equality of the two functions, almost
everywhere on `(0, ∞)`.

The route is Laplace determinacy in the form already owned by the corpus.  With
`g := 1_{(0,∞)} · (𝔓_· - P_·) · e^{-σ₁ ·}` for `σ₁ = 3 + max(Im z, 0)`, the growth bounds
`exists_expBound_suzukiFrakP` and `norm_suzukiPtZeroSum_le` give `‖g x‖ ≤ K e^{-|x|}`, while the
Laplace identity says exactly that the exponential Fourier transform `expFourier g` vanishes at
`iτ` for every real `|τ| < 2`.  Analyticity of `expFourier g` on the strip
(`RHTower.analyticOnNhd_expFourier`) turns that segment of zeros into a full neighbourhood of `0`
(`expFourier_eventuallyEq_zero_of_imaginarySegment`), and the tail of
`RHTower.ae_eq_zero_of_moments_eq_zero`, isolated here as
`ae_eq_zero_of_expFourier_eventuallyEq_zero`, finishes.

Everything here is unconditional.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Exponential growth bound for `𝔓_t` -/

theorem exp_mul_le_exp_mul {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t) :
    Real.exp (a * t) ≤ Real.exp (b * t) :=
  Real.exp_le_exp.mpr (by nlinarith)

theorem norm_suzukiFrakPPolar_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖suzukiFrakPPolar t z‖
      ≤ (8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ + 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹) * Real.exp (t / 2) := by
  have hE : (1 : ℝ) ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  have hb1 : ‖((Real.exp (t / 2) : ℝ) : ℂ) - 1‖ ≤ 2 * Real.exp (t / 2) := by
    calc ‖((Real.exp (t / 2) : ℝ) : ℂ) - 1‖
        ≤ ‖((Real.exp (t / 2) : ℝ) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (t / 2) + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, norm_one]
      _ ≤ 2 * Real.exp (t / 2) := by linarith
  have hb2 : ‖((Real.exp (-(t / 2)) : ℝ) : ℂ) - 1‖ ≤ 1 := by
    have hpos : (0 : ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
    have hle : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [show ((Real.exp (-(t / 2)) : ℝ) : ℂ) - 1 = (((Real.exp (-(t / 2)) - 1 : ℝ)) : ℂ) by
      push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have h1 : ‖4 * ((Real.exp (t / 2) : ℂ) - 1) / ((1 : ℂ) + 2 * I * z)‖
      ≤ 8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ * Real.exp (t / 2) := by
    rw [norm_div, norm_mul, div_eq_mul_inv, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hinv : (0 : ℝ) ≤ ‖(1 : ℂ) + 2 * I * z‖⁻¹ := by positivity
    calc 4 * ‖((Real.exp (t / 2) : ℝ) : ℂ) - 1‖ * ‖(1 : ℂ) + 2 * I * z‖⁻¹
        ≤ 4 * (2 * Real.exp (t / 2)) * ‖(1 : ℂ) + 2 * I * z‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ hinv
          linarith
      _ = 8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ * Real.exp (t / 2) := by ring
  have h2 : ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / ((1 : ℂ) - 2 * I * z)‖
      ≤ 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ * Real.exp (t / 2) := by
    rw [norm_div, norm_mul, div_eq_mul_inv, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hinv : (0 : ℝ) ≤ ‖(1 : ℂ) - 2 * I * z‖⁻¹ := by positivity
    calc 4 * ‖((Real.exp (-(t / 2)) : ℝ) : ℂ) - 1‖ * ‖(1 : ℂ) - 2 * I * z‖⁻¹
        ≤ 4 * 1 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ hinv
          linarith
      _ ≤ 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ * Real.exp (t / 2) := by
          have : (0 : ℝ) ≤ 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ := by positivity
          nlinarith
  calc ‖suzukiFrakPPolar t z‖
      ≤ ‖4 * ((Real.exp (t / 2) : ℂ) - 1) / ((1 : ℂ) + 2 * I * z)‖
        + ‖4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / ((1 : ℂ) - 2 * I * z)‖ := norm_add_le _ _
    _ ≤ 8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ * Real.exp (t / 2)
        + 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ * Real.exp (t / 2) := by linarith
    _ = (8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ + 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹) * Real.exp (t / 2) := by ring

theorem norm_suzukiFrakPZeta_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖suzukiFrakPZeta t z‖
      ≤ 2 * ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖ * ‖z‖⁻¹
        * Real.exp (max z.im 0 * t) := by
  set m : ℝ := max z.im 0 with hm
  have hmnn : (0 : ℝ) ≤ m := le_max_right _ _
  have hexp : ‖Complex.exp (-(I * z * (t : ℂ)))‖ ≤ Real.exp (m * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [re_neg_I_mul_ofReal]
    rcases le_total 0 z.im with him | him
    · rw [hm, max_eq_left him]
      nlinarith
    · rw [hm, max_eq_right him]
      nlinarith
  have hb : ‖Complex.exp (-(I * z * (t : ℂ))) - 1‖ ≤ 2 * Real.exp (m * t) := by
    have h1 : (1 : ℝ) ≤ Real.exp (m * t) := Real.one_le_exp (by positivity)
    calc ‖Complex.exp (-(I * z * (t : ℂ))) - 1‖
        ≤ ‖Complex.exp (-(I * z * (t : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (m * t) + 1 := by rw [norm_one]; linarith
      _ ≤ 2 * Real.exp (m * t) := by linarith
  rw [suzukiFrakPZeta, norm_mul, norm_div, norm_mul, norm_I, one_mul]
  have hinv : (0 : ℝ) ≤ ‖z‖⁻¹ := by positivity
  have hL : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖ := norm_nonneg _
  rw [div_eq_mul_inv]
  calc ‖Complex.exp (-(I * z * (t : ℂ))) - 1‖ * ‖z‖⁻¹
        * ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖
      ≤ (2 * Real.exp (m * t)) * ‖z‖⁻¹
        * ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hinv) hL
    _ = 2 * ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖ * ‖z‖⁻¹ * Real.exp (m * t) := by ring


theorem norm_suzukiFrakPLerch_le {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    ‖suzukiFrakPLerch t z‖
      ≤ (∑' n : ℕ, ‖((n : ℂ) + ((1 : ℂ) / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖)
          / (2 * ‖z‖) := by
  have hhalf : ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hden : ‖(2 : ℂ) * I * z‖ = 2 * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_I, mul_one]
    simp
  rw [suzukiFrakPLerch, norm_neg, norm_div, norm_mul, hden]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)‖ * ‖suzukiLerchDiff t ((1 : ℂ) / 4 - I * z / 2)‖
      ≤ 1 * (∑' n : ℕ, ‖((n : ℂ) + ((1 : ℂ) / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖) :=
        mul_le_mul hhalf (norm_suzukiLerchDiff_le ht hw) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Exponential growth bound for Suzuki's `𝔓_t`.** -/
theorem exists_expBound_suzukiFrakP {z : ℂ} (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖suzukiFrakP t z‖ ≤ C * Real.exp ((2 + max z.im 0) * t) := by
  set m : ℝ := max z.im 0 with hm
  have hmnn : (0 : ℝ) ≤ m := le_max_right _ _
  set C₁ : ℝ := 8 * ‖(1 : ℂ) + 2 * I * z‖⁻¹ + 4 * ‖(1 : ℂ) - 2 * I * z‖⁻¹ with hC₁
  set C₂ : ℝ := 2 * ‖logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)‖ * ‖z‖⁻¹ with hC₂
  set C₃ : ℝ := 2 * ‖z‖⁻¹ with hC₃
  set C₄ : ℝ := ‖suzukiFrakPDigamma z‖ with hC₄
  set C₅ : ℝ := (∑' n : ℕ, ‖((n : ℂ) + ((1 : ℂ) / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖)
      / (2 * ‖z‖) with hC₅
  have hC₁nn : (0 : ℝ) ≤ C₁ := by rw [hC₁]; positivity
  have hC₂nn : (0 : ℝ) ≤ C₂ := by rw [hC₂]; positivity
  have hC₃nn : (0 : ℝ) ≤ C₃ := by rw [hC₃]; positivity
  have hC₄nn : (0 : ℝ) ≤ C₄ := by rw [hC₄]; positivity
  have hC₅nn : (0 : ℝ) ≤ C₅ := by
    rw [hC₅]
    have : (0 : ℝ) ≤ ∑' n : ℕ, ‖((n : ℂ) + ((1 : ℂ) / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ :=
      tsum_nonneg fun n => norm_nonneg _
    positivity
  refine ⟨C₁ + C₂ + C₃ + C₄ + C₅, by positivity, fun t ht => ?_⟩
  have hone : (1 : ℝ) ≤ Real.exp ((2 + m) * t) := Real.one_le_exp (by positivity)
  have hb1 : ‖suzukiFrakPPolar t z‖ ≤ C₁ * Real.exp ((2 + m) * t) := by
    refine (norm_suzukiFrakPPolar_le ht z).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁nn
    have : Real.exp (t / 2) = Real.exp ((1 / 2 : ℝ) * t) := by congr 1; ring
    rw [this]
    exact exp_mul_le_exp_mul (by linarith) ht
  have hb2 : ‖suzukiFrakPZeta t z‖ ≤ C₂ * Real.exp ((2 + m) * t) := by
    refine (norm_suzukiFrakPZeta_le ht z).trans ?_
    refine mul_le_mul_of_nonneg_left (exp_mul_le_exp_mul (by linarith) ht) hC₂nn
  have hb3 : ‖suzukiFrakPPrime t z‖ ≤ C₃ * Real.exp ((2 + m) * t) := by
    refine (norm_suzukiFrakPPrime_le ht z).trans ?_
    have hte : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hmt : (1 : ℝ) ≤ Real.exp (t * m) := Real.one_le_exp (by positivity)
    have hsplit : Real.exp t * t * (Real.exp (t * m) + 1) ≤ 2 * Real.exp ((2 + m) * t) := by
      have h2 : Real.exp t * Real.exp t * (2 * Real.exp (t * m))
          = 2 * Real.exp ((2 + m) * t) := by
        rw [show Real.exp t * Real.exp t * (2 * Real.exp (t * m))
            = 2 * (Real.exp t * Real.exp t * Real.exp (t * m)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      calc Real.exp t * t * (Real.exp (t * m) + 1)
          ≤ Real.exp t * Real.exp t * (Real.exp (t * m) + 1) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hte (Real.exp_pos t).le) (by positivity)
        _ ≤ Real.exp t * Real.exp t * (2 * Real.exp (t * m)) := by
            refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 2 * Real.exp ((2 + m) * t) := h2
    calc Real.exp t * t * (Real.exp (t * m) + 1) / ‖z‖
        ≤ 2 * Real.exp ((2 + m) * t) / ‖z‖ := div_le_div_of_nonneg_right hsplit (norm_nonneg z)
      _ = C₃ * Real.exp ((2 + m) * t) := by rw [hC₃]; ring
  have hb4 : ‖suzukiFrakPDigamma z‖ ≤ C₄ * Real.exp ((2 + m) * t) := by
    rw [hC₄]
    nlinarith [norm_nonneg (suzukiFrakPDigamma z)]
  have hb5 : ‖suzukiFrakPLerch t z‖ ≤ C₅ * Real.exp ((2 + m) * t) := by
    refine (norm_suzukiFrakPLerch_le ht hw).trans ?_
    rw [← hC₅]
    nlinarith [hC₅nn]
  calc ‖suzukiFrakP t z‖
      ≤ ‖suzukiFrakPPolar t z‖ + ‖suzukiFrakPZeta t z‖ + ‖suzukiFrakPPrime t z‖
        + ‖suzukiFrakPDigamma z‖ + ‖suzukiFrakPLerch t z‖ := by
        rw [suzukiFrakP_eq_blocks]
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ (C₁ + C₂ + C₃ + C₄ + C₅) * Real.exp ((2 + m) * t) := by
        rw [add_mul, add_mul, add_mul, add_mul]
        linarith


/-! ## Determinacy from a vanishing exponential Fourier transform -/

/-- The tail of `ae_eq_zero_of_moments_eq_zero`, isolated: an exponentially decaying function whose
exponential Fourier transform vanishes near the origin vanishes almost everywhere. -/
theorem ae_eq_zero_of_expFourier_eventuallyEq_zero {g : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable g volume) {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    (hev : expFourier g =ᶠ[𝓝 (0 : ℂ)] 0) :
    g =ᵐ[volume] 0 := by
  have hzero : (0 : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.zero_im, abs_zero]
    exact hε
  have hstrip : Set.EqOn (expFourier g) 0 {w : ℂ | |w.im| < ε} :=
    (analyticOnNhd_expFourier hmeas hK0 hbound).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_imStrip ε).isPreconnected hzero hev
  refine integrable_ae_eq_zero_of_fourier_eq_zero
    (integrable_of_expDecay hmeas hε hbound) (fun w => ?_)
  have hmem : (((2 * Real.pi * w : ℝ)) : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
    exact hε
  have hval : expFourier g (((2 * Real.pi * w : ℝ)) : ℂ) = 0 := by
    simpa using hstrip hmem
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [expFourier] at hval
  rw [← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- Vanishing of the exponential Fourier transform along the imaginary axis near the origin already
forces it to vanish on a full neighbourhood. -/
theorem expFourier_eventuallyEq_zero_of_imaginarySegment {g : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable g volume) {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    (hseg : ∀ᶠ (τ : ℝ) in 𝓝[≠] (0 : ℝ), expFourier g (I * ((τ : ℝ) : ℂ)) = 0) :
    expFourier g =ᶠ[𝓝 (0 : ℂ)] 0 := by
  have hzero : (0 : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.zero_im, abs_zero]
    exact hε
  have hat : AnalyticAt ℂ (expFourier g) 0 :=
    (analyticOnNhd_expFourier hmeas hK0 hbound) 0 hzero
  rcases hat.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact h
  · exfalso
    have htend : Tendsto (fun τ : ℝ => I * (τ : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hc : Continuous (fun τ : ℝ => I * (τ : ℂ)) := by fun_prop
        have h0 : Tendsto (fun τ : ℝ => I * (τ : ℂ)) (𝓝 (0 : ℝ))
            (𝓝 (I * ((0 : ℝ) : ℂ))) := hc.tendsto 0
        have h0' : I * ((0 : ℝ) : ℂ) = 0 := by simp
        rw [h0'] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hτ ⊢
        intro hc
        rcases mul_eq_zero.mp hc with h1 | h1
        · exact Complex.I_ne_zero h1
        · exact hτ (by exact_mod_cast h1)
    obtain ⟨τ, hnz, hz⟩ := ((htend.eventually h).and hseg).exists
    exact hnz hz


/-! ## Measurability in the time variable -/

theorem measurable_suzukiPtZeroSum (z : ℂ) : Measurable (fun t : ℝ => suzukiPtZeroSum t z) := by
  refine Measurable.tsum fun q => ?_
  show Measurable fun t : ℝ =>
    (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) /
      (xiSpectralPoint q * (z - xiSpectralPoint q))
  fun_prop

theorem measurable_suzukiFrakPPrimeBlock (z : ℂ) :
    Measurable (fun t : ℝ => suzukiFrakPPrime t z) := by
  have hfun : (fun t : ℝ => suzukiFrakPPrime t z)
      = fun t : ℝ => ∑' n : ℕ, suzukiPrimeRayTerm z n t := by
    funext t
    exact suzukiFrakPPrime_eq_tsum t z
  rw [hfun]
  refine Measurable.tsum fun n => ?_
  have hind : (fun t : ℝ => suzukiPrimeRayTerm z n t)
      = Set.indicator (Ici (Real.log n)) (fun t : ℝ =>
          (screwPrimeWeight n : ℂ) *
            ((Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1) / (I * z))) := by
    funext t
    rw [suzukiPrimeRayTerm, Set.indicator_apply]
    by_cases h : Real.log n ≤ t
    · rw [if_pos h, if_pos (by exact h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  show Measurable (fun t : ℝ => suzukiPrimeRayTerm z n t)
  rw [hind]
  refine Measurable.indicator ?_ measurableSet_Ici
  fun_prop

theorem measurable_suzukiFrakPLerchBlock (z : ℂ) :
    Measurable (fun t : ℝ => suzukiFrakPLerch t z) := by
  have hmeas : Measurable (fun t : ℝ => suzukiLerchDiff t ((1 : ℂ) / 4 - I * z / 2)) := by
    refine Measurable.tsum fun n => ?_
    show Measurable fun t : ℝ => (Real.exp (-(2 * (n : ℝ) * t)) : ℂ) *
      (((n : ℂ) + ((1 : ℂ) / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)
    fun_prop
  show Measurable fun t : ℝ =>
    -((Real.exp (-(t / 2)) : ℂ) * suzukiLerchDiff t ((1 : ℂ) / 4 - I * z / 2) / (2 * I * z))
  fun_prop

theorem measurable_suzukiFrakP (z : ℂ) : Measurable (fun t : ℝ => suzukiFrakP t z) := by
  have hfun : (fun t : ℝ => suzukiFrakP t z)
      = fun t : ℝ => suzukiFrakPPolar t z + suzukiFrakPZeta t z + suzukiFrakPPrime t z
        + suzukiFrakPDigamma z + suzukiFrakPLerch t z := by
    funext t
    exact suzukiFrakP_eq_blocks t z
  rw [hfun]
  have h1 : Measurable (fun t : ℝ => suzukiFrakPPolar t z) := by
    show Measurable fun t : ℝ =>
      4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)
        + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)
    fun_prop
  have h2 : Measurable (fun t : ℝ => suzukiFrakPZeta t z) := by
    show Measurable fun t : ℝ =>
      (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) * logDeriv riemannZeta (1 / 2 - I * z)
    fun_prop
  exact ((((h1.add h2).add (measurable_suzukiFrakPPrimeBlock z)).add measurable_const).add
    (measurable_suzukiFrakPLerchBlock z))


theorem integrableOn_suzukiFrakP_laplace {σ : ℝ} {z : ℂ}
    (hσ1 : 1 / 2 < σ) (hσ2 : 1 + max z.im 0 < σ) (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    IntegrableOn (fun t : ℝ => suzukiFrakP t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hmnn : (0 : ℝ) ≤ max z.im 0 := le_max_right _ _
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hz : z.im < σ := lt_of_le_of_lt (le_max_left _ _) (by linarith)
  have hI1 := integrableOn_suzukiFrakPPolar_laplace hσ1 z
  have hI2 := integrableOn_suzukiFrakPZeta_laplace hσ0 hz
  have hI3 := integrableOn_suzukiFrakPPrime_laplace z hσ2
  have hI4 := integrableOn_suzukiFrakPDigamma_laplace hσ0 z
  have hI5 := integrableOn_suzukiFrakPLerch_laplace hσ0 hw
  refine ((((hI1.add hI2).add hI3).add hI4).add hI5).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  rw [suzukiFrakP_eq_blocks]
  ring

theorem integrableOn_suzukiPtZeroSum_laplace {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ with hS
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hS]
    exact tsum_nonneg fun q => norm_nonneg _
  have hrate : (0 : ℝ) < σ - 1 / 2 := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => 2 * S * Real.exp (-((σ - 1 / 2) * t)))
      (Ioi (0 : ℝ)) volume := by
    refine Integrable.const_mul ?_ _
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hrate).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  refine MeasureTheory.Integrable.mono' hmaj
    (((measurable_suzukiPtZeroSum z).mul (by fun_prop)).aestronglyMeasurable.restrict) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have htnn : (0 : ℝ) ≤ t := le_of_lt ht
  have hexp : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [norm_mul, hexp]
  have hP := norm_suzukiPtZeroSum_le t z
  rw [← hS] at hP
  have habs : |t| = t := abs_of_nonneg htnn
  rw [habs] at hP
  have hsplit : (Real.exp (t / 2) + 1) * Real.exp (-(σ * t))
      ≤ 2 * Real.exp (-((σ - 1 / 2) * t)) := by
    have h1 : (1 : ℝ) ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
    have h2 : Real.exp (t / 2) * Real.exp (-(σ * t)) = Real.exp (-((σ - 1 / 2) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [Real.exp_pos (-(σ * t)), h2]
  calc ‖suzukiPtZeroSum t z‖ * Real.exp (-(σ * t))
      ≤ ((Real.exp (t / 2) + 1) * S) * Real.exp (-(σ * t)) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ = S * ((Real.exp (t / 2) + 1) * Real.exp (-(σ * t))) := by ring
    _ ≤ S * (2 * Real.exp (-((σ - 1 / 2) * t))) := mul_le_mul_of_nonneg_left hsplit hSnn
    _ = 2 * S * Real.exp (-((σ - 1 / 2) * t)) := by ring

/-- **Suzuki, Proposition 3.1, almost-everywhere form.**  The prime--archimedean expression `𝔓_t(z)`
and the Xi-zero series `P_t(z)` agree for almost every `t > 0`. -/
theorem suzukiFrakP_ae_eq_suzukiPtZeroSum {z : ℂ} (hz0 : z ≠ 0)
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) (hs1 : (1 : ℂ) / 2 - I * z ≠ 1) (hXi : XiC z ≠ 0) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), suzukiFrakP t z = suzukiPtZeroSum t z := by
  set m : ℝ := max z.im 0 with hm
  have hmnn : (0 : ℝ) ≤ m := le_max_right _ _
  set σ₁ : ℝ := 3 + m with hσ₁
  obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_expBound_suzukiFrakP hw
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ with hS
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hS]
    exact tsum_nonneg fun q => norm_nonneg _
  set K : ℝ := C₁ + 2 * S with hK
  have hKnn : (0 : ℝ) ≤ K := by rw [hK]; positivity
  -- the exponentially damped difference
  set F : ℝ → ℂ := fun t : ℝ =>
    (suzukiFrakP t z - suzukiPtZeroSum t z) * Complex.exp (-((σ₁ : ℂ) * (t : ℂ))) with hF
  set g : ℝ → ℂ := Set.indicator (Ioi (0 : ℝ)) F with hg
  have hbnd : ∀ t : ℝ, 0 ≤ t →
      ‖suzukiFrakP t z - suzukiPtZeroSum t z‖ ≤ K * Real.exp ((2 + m) * t) := by
    intro t ht
    have hP : ‖suzukiPtZeroSum t z‖ ≤ 2 * S * Real.exp ((2 + m) * t) := by
      refine (norm_suzukiPtZeroSum_le t z).trans ?_
      rw [← hS]
      have h1 : Real.exp (|t| / 2) + 1 ≤ 2 * Real.exp ((2 + m) * t) := by
        have habs : |t| = t := abs_of_nonneg ht
        rw [habs]
        have h2 : Real.exp (t / 2) ≤ Real.exp ((2 + m) * t) := by
          rw [show t / 2 = (1 / 2 : ℝ) * t by ring]
          exact exp_mul_le_exp_mul (by linarith) ht
        have h3 : (1 : ℝ) ≤ Real.exp ((2 + m) * t) := Real.one_le_exp (by positivity)
        linarith
      nlinarith [hSnn]
    have hF' := hC₁ t ht
    calc ‖suzukiFrakP t z - suzukiPtZeroSum t z‖
        ≤ ‖suzukiFrakP t z‖ + ‖suzukiPtZeroSum t z‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.exp ((2 + m) * t) + 2 * S * Real.exp ((2 + m) * t) := by linarith
      _ = K * Real.exp ((2 + m) * t) := by rw [hK]; ring
  have hgb : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(1 * |x|)) := by
    intro x
    rw [hg, Set.indicator_apply]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [if_pos hx]
      have hxpos : (0 : ℝ) < x := hx
      have hexp : ‖Complex.exp (-((σ₁ : ℂ) * (x : ℂ)))‖ = Real.exp (-(σ₁ * x)) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      rw [hF, norm_mul, hexp]
      have habs : |x| = x := abs_of_nonneg hxpos.le
      rw [habs]
      have hkey : Real.exp ((2 + m) * x) * Real.exp (-(σ₁ * x)) = Real.exp (-(1 * x)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hσ₁]
        ring
      calc ‖suzukiFrakP x z - suzukiPtZeroSum x z‖ * Real.exp (-(σ₁ * x))
          ≤ (K * Real.exp ((2 + m) * x)) * Real.exp (-(σ₁ * x)) :=
            mul_le_mul_of_nonneg_right (hbnd x hxpos.le) (Real.exp_pos _).le
        _ = K * Real.exp (-(1 * x)) := by rw [mul_assoc, hkey]
    · rw [if_neg hx, norm_zero]
      positivity
  have hgmeas : Measurable g := by
    rw [hg]
    refine Measurable.indicator ?_ measurableSet_Ioi
    rw [hF]
    exact (((measurable_suzukiFrakP z).sub (measurable_suzukiPtZeroSum z)).mul (by fun_prop))
  -- the exponential Fourier transform vanishes along the imaginary axis
  have hseg : ∀ᶠ (τ : ℝ) in 𝓝[≠] (0 : ℝ), expFourier g (I * ((τ : ℝ) : ℂ)) = 0 := by
    have hball : ∀ᶠ (τ : ℝ) in 𝓝[≠] (0 : ℝ), |τ| < 2 := by
      have hb : ∀ᶠ (τ : ℝ) in 𝓝 (0 : ℝ), |τ| < 2 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 2)] with τ hτ
        simpa [Real.dist_eq] using hτ
      exact hb.filter_mono nhdsWithin_le_nhds
    filter_upwards [hball] with τ hτ
    have hτ2 : τ < 2 := (abs_lt.mp hτ).2
    have hσ : (1 : ℝ) + m < σ₁ - τ := by rw [hσ₁]; linarith
    have hσh : (1 : ℝ) / 2 < σ₁ - τ := by linarith
    have hkernel : ∀ x : ℝ, g x * Complex.exp (-(I * (I * ((τ : ℝ) : ℂ)) * (x : ℂ)))
        = Set.indicator (Ioi (0 : ℝ)) (fun t : ℝ =>
            (suzukiFrakP t z - suzukiPtZeroSum t z) *
              Complex.exp (-(((σ₁ - τ : ℝ) : ℂ) * (t : ℂ)))) x := by
      intro x
      rw [hg, Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · rw [if_pos hx, if_pos hx, hF]
        have hexp : Complex.exp (-(I * (I * ((τ : ℝ) : ℂ)) * (x : ℂ)))
            = Complex.exp (((τ : ℝ) : ℂ) * (x : ℂ)) := by
          congr 1
          linear_combination (-((τ : ℝ) : ℂ) * (x : ℂ)) * Complex.I_sq
        rw [hexp, mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      · rw [if_neg hx, if_neg hx, zero_mul]
    rw [expFourier]
    rw [integral_congr_ae (Filter.Eventually.of_forall hkernel)]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
    have hIP := integrableOn_suzukiFrakP_laplace (z := z) (σ := σ₁ - τ) hσh (by rw [← hm]; linarith) hw
    have hIZ := integrableOn_suzukiPtZeroSum_laplace (σ := σ₁ - τ) hσh z
    have hsplit : ∀ t : ℝ,
        (suzukiFrakP t z - suzukiPtZeroSum t z) *
            Complex.exp (-(((σ₁ - τ : ℝ) : ℂ) * (t : ℂ)))
          = suzukiFrakP t z * Complex.exp (-(((σ₁ - τ : ℝ) : ℂ) * (t : ℂ)))
            - suzukiPtZeroSum t z * Complex.exp (-(((σ₁ - τ : ℝ) : ℂ) * (t : ℂ))) := by
      intro t
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hsplit t),
      MeasureTheory.integral_sub hIP hIZ,
      integral_suzukiFrakP_laplace_eq_zeroSeries hz0 hσh (by rw [← hm]; linarith) hw hs1 hXi,
      sub_self]
  -- determinacy
  have hzero := ae_eq_zero_of_expFourier_eventuallyEq_zero hgmeas.aestronglyMeasurable hKnn
    (by norm_num : (0 : ℝ) < 1) hgb
    (expFourier_eventuallyEq_zero_of_imaginarySegment hgmeas.aestronglyMeasurable hKnn
      (by norm_num : (0 : ℝ) < 1) hgb hseg)
  have hres : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g t = 0 :=
    ae_restrict_of_ae hzero
  filter_upwards [hres, self_mem_ae_restrict measurableSet_Ioi] with t hgt htmem
  rw [hg, Set.indicator_of_mem htmem, hF] at hgt
  have hexpne : Complex.exp (-((σ₁ : ℂ) * (t : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have := mul_eq_zero.mp hgt
  rcases this with h | h
  · linear_combination h
  · exact absurd h hexpne

end
end RHTower
