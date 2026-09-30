import GaloisForLFunctions.RHTower.WeilFullConeConvolutionPositivity
import GaloisForLFunctions.RHTower.XiWindowZeroCount

/-!
# Spectral localization of the Riemann kernel on zero-free windows

With Mathlib's transform `𝓕f(ξ) = ∫ e^{−2πixξ} f(x) dx`, write `X = 𝓕Φ`.
- `X(ξ) = XiC(2πξ) = Ξ(2πξ)` is real and smooth (`phiFourier_eq_XiC`, `contDiff_phiFourier`).
- `𝓕K = X²` (`fourier_riemannAutocorr_eq`), and `X² ∈ L¹` by one integration by parts.
- Hence `K(z) = ∫ X(ξ)² e^{2πizξ} dξ`, and
  `riemannPairForm K g y = ∫ X(ξ)² |𝓕g(ξ)|² e^{2πiξy} dξ` (`riemannPairForm_eq_integral_fourier`).

**Localization.** Let `φ(x) = S(1/4 − x²)` be an even bump (`localBump`) and
`B(x) = ∫ φ(s)² cos(2πsx) ds` (`bumpCos`). If `X` has no zero within `η` of `ξ₀`, then
`u = φ((ξ − ξ₀)/η)/X` is smooth and compactly supported, and `g = 𝓕⁻u` is a Schwartz function
with `X²|𝓕g|² = φ((·−ξ₀)/η)²`.

**Theorem** (`localized_deviation_nonneg`). For every full-cone Weil-positive `lam` with bounded
deviation `v` and `Σ|v(n)|(1 + |log n|)^{−k} < ∞`:
`Σ_n v(n) B(η log n) cos(2πξ₀ log n) ≥ 0` whenever `X ≠ 0` on `(ξ₀ − η, ξ₀ + η)`.

`B` is real, even, bounded by `B(0) = ∫φ² > 0`, continuous and rapidly decaying
(`exists_abs_bumpCos_le`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## The spectral side: `𝓕K = X²` -/

theorem fourier_apply_eq_integral_cexp (h : ℝ → ℂ) (w : ℝ) :
    𝓕 h w = ∫ v, Complex.exp (-((2 * π * v * w : ℝ) : ℂ) * I) * h v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]; congr 2; push_cast; ring

theorem fourierInv_apply_eq_integral_cexp (h : ℝ → ℂ) (w : ℝ) :
    𝓕⁻ h w = ∫ v, Complex.exp (((2 * π * v * w : ℝ) : ℂ) * I) * h v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 3; ring_nf

/-- `X(ξ) = 𝓕Φ(ξ)`. -/
def phiFourier (ξ : ℝ) : ℂ := 𝓕 riemannPhiKernel ξ

theorem phiFourier_eq_XiC (ξ : ℝ) : phiFourier ξ = XiC (2 * π * ξ) := by
  have h1 := paperFT_riemannPhiKernel (-(2 * π * ξ : ℂ))
  rw [riemannPhiTransform_eq_xi] at h1
  have h2 : xi (1 / 2 + I * -(2 * π * ξ : ℂ)) = XiC (2 * π * ξ) := by
    rw [← XiC_even]; unfold XiC; congr 1; ring
  rw [h2] at h1
  rw [← h1, phiFourier, fourier_apply_eq_integral_cexp]
  unfold Zeta23.paperFT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  rw [mul_comm]; push_cast; ring_nf

/-- `X` is real: `X(ξ) = Ξ(2πξ)`. -/
def phiFourierReal (ξ : ℝ) : ℝ := Xi (2 * π * ξ)

theorem phiFourier_eq_ofReal (ξ : ℝ) : phiFourier ξ = (phiFourierReal ξ : ℂ) := by
  rw [phiFourier_eq_XiC, phiFourierReal, ← XiC_ofReal]; push_cast; ring_nf

theorem riemannKernelReal_neg_eq (u : ℝ) : riemannKernelReal (-u) = riemannKernelReal u := by
  simp [riemannKernelReal, abs_neg]

/-- `K` as a complex function is the self-convolution of `Φ`. -/
theorem riemannAutocorr_eq_convolution' (y : ℝ) :
    ((riemannAutocorr y : ℝ) : ℂ) =
      (riemannPhiKernel ⋆[ContinuousLinearMap.mul ℂ ℂ] riemannPhiKernel) y := by
  rw [convolution_def, riemannAutocorr, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', riemannPhiKernel_eq_ofReal]
  rw [show y - t = -(t - y) by ring, riemannKernelReal_neg_eq]
  push_cast; ring

/-- **`𝓕K = X²`.** -/
theorem fourier_riemannAutocorr_eq (ξ : ℝ) :
    𝓕 (fun y => ((riemannAutocorr y : ℝ) : ℂ)) ξ = phiFourier ξ ^ 2 := by
  have h : (fun y => ((riemannAutocorr y : ℝ) : ℂ)) =
      riemannPhiKernel ⋆[ContinuousLinearMap.mul ℂ ℂ] riemannPhiKernel :=
    funext riemannAutocorr_eq_convolution'
  rw [h, Real.fourier_mul_convolution_eq integrable_riemannPhiKernel integrable_riemannPhiKernel,
    sq]
  rfl


theorem deriv_riemannPhiKernel : deriv riemannPhiKernel = riemannKernelDeriv 1 := by
  funext u; rw [← riemannKernelDeriv_zero]; exact (hasDerivAt_riemannKernelDeriv 0 u).deriv

theorem differentiable_riemannPhiKernel : Differentiable ℝ riemannPhiKernel := fun u => by
  rw [← riemannKernelDeriv_zero]; exact (hasDerivAt_riemannKernelDeriv 0 u).differentiableAt

theorem continuous_fourier_of_integrable_real {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

theorem continuous_phiFourier : Continuous phiFourier :=
  continuous_fourier_of_integrable_real integrable_riemannPhiKernel

theorem norm_fourier_le_integral_norm' (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ u, ‖f u‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem abs_mul_norm_phiFourier_le (ξ : ℝ) :
    2 * π * |ξ| * ‖phiFourier ξ‖ ≤ ∫ u, ‖riemannKernelDeriv 1 u‖ := by
  have h := Real.fourier_deriv integrable_riemannPhiKernel differentiable_riemannPhiKernel
    (by rw [deriv_riemannPhiKernel]; exact (superExpDecay_riemannKernelDeriv 1).integrable)
  have h2 := congrFun h ξ
  rw [deriv_riemannPhiKernel] at h2
  have h3 := norm_fourier_le_integral_norm' (riemannKernelDeriv 1) ξ
  rw [h2, norm_smul] at h3
  have e : ‖(2 * (π : ℂ) * I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
  rw [e] at h3
  exact h3

/-- `X² ∈ L¹`. -/
theorem integrable_phiFourier_sq : Integrable fun ξ => phiFourier ξ ^ 2 := by
  set A0 := ∫ u, ‖riemannPhiKernel u‖ with hA0
  set A1 := ∫ u, ‖riemannKernelDeriv 1 u‖ with hA1
  have hπ := Real.pi_pos
  refine (integrable_inv_one_add_sq.const_mul (A0 ^ 2 + (A1 / (2 * π)) ^ 2)).mono'
    (continuous_phiFourier.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have h0 : ‖phiFourier ξ‖ ≤ A0 := norm_fourier_le_integral_norm' _ ξ
  have h1 : |ξ| * ‖phiFourier ξ‖ ≤ A1 / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := abs_mul_norm_phiFourier_le ξ
    linarith
  have hn0 := norm_nonneg (phiFourier ξ)
  have hsq : (1 + ξ ^ 2) * ‖phiFourier ξ‖ ^ 2 ≤ A0 ^ 2 + (A1 / (2 * π)) ^ 2 := by
    have e : (1 + ξ ^ 2) * ‖phiFourier ξ‖ ^ 2 = ‖phiFourier ξ‖ ^ 2 + (|ξ| * ‖phiFourier ξ‖) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [e]
    have ha : 0 ≤ |ξ| * ‖phiFourier ξ‖ := by positivity
    nlinarith [pow_le_pow_left₀ hn0 h0 2, pow_le_pow_left₀ ha h1 2]
  rw [norm_pow, le_mul_inv_iff₀ (by positivity), mul_comm]
  exact hsq

theorem integrable_riemannAutocorr_complex :
    Integrable fun y => ((riemannAutocorr y : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le_exp
  refine (integrable_exp_neg_abs.const_mul C).mono'
    (Complex.continuous_ofReal.comp riemannAutocorr_continuous).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg y)]
  refine (hC y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
  linarith [abs_nonneg y]

/-- **Fourier inversion for `K`:** `K(z) = ∫ X(ξ)² e^{2πizξ} dξ`. -/
theorem riemannAutocorr_eq_integral (z : ℝ) :
    ((riemannAutocorr z : ℝ) : ℂ) =
      ∫ ξ, Complex.exp (((2 * π * ξ * z : ℝ) : ℂ) * I) * phiFourier ξ ^ 2 := by
  have hc : Continuous fun y => ((riemannAutocorr y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp riemannAutocorr_continuous
  have hF : 𝓕 (fun y => ((riemannAutocorr y : ℝ) : ℂ)) = fun ξ => phiFourier ξ ^ 2 :=
    funext fourier_riemannAutocorr_eq
  have h := hc.fourierInv_fourier_eq integrable_riemannAutocorr_complex
    (by rw [hF]; exact integrable_phiFourier_sq)
  have h2 := congrFun h z
  rw [hF, fourierInv_apply_eq_integral_cexp] at h2
  exact h2.symm


/-- The character `e(ξ, z) = e^{2πiξz}`. -/
def spectralChar (ξ z : ℝ) : ℂ := Complex.exp (((2 * π * ξ * z : ℝ) : ℂ) * I)

theorem continuous_spectralChar : Continuous fun p : ℝ × ℝ => spectralChar p.1 p.2 := by
  unfold spectralChar; fun_prop

theorem norm_spectralChar (ξ z : ℝ) : ‖spectralChar ξ z‖ = 1 := by
  unfold spectralChar; rw [Complex.norm_exp_ofReal_mul_I]

theorem spectralChar_add (ξ a b : ℝ) : spectralChar ξ (a + b) = spectralChar ξ a * spectralChar ξ b := by
  unfold spectralChar; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem conj_fourier_eq_integral (g : ℝ → ℂ) (ξ : ℝ) :
    conj (𝓕 g ξ) = ∫ w, conj (g w) * spectralChar ξ w := by
  rw [fourier_apply_eq_integral_cexp, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [spectralChar]
  rw [map_mul, ← Complex.exp_conj, mul_comm]
  congr 2
  rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem fourier_eq_integral_spectralChar (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 g ξ = ∫ v, g v * spectralChar ξ (-v) := by
  rw [fourier_apply_eq_integral_cexp]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [spectralChar]
  rw [mul_comm]; congr 2; push_cast; ring

/-- **The spectral form of the pairing:**
`riemannPairForm K g y = ∫ X(ξ)² |𝓕g(ξ)|² e^{2πiξy} dξ`. -/
theorem riemannPairForm_eq_integral_fourier {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    (y : ℝ) :
    riemannPairForm riemannAutocorr g y =
      ∫ ξ, phiFourier ξ ^ 2 * (𝓕 g ξ * conj (𝓕 g ξ)) * spectralChar ξ y := by
  have hX := integrable_phiFourier_sq
  have hXc : Continuous fun ξ => phiFourier ξ ^ 2 := continuous_phiFourier.pow 2
  have hFg := continuous_fourier_of_integrable_real hgi
  set N := ∫ u, ‖g u‖ with hN
  unfold riemannPairForm
  have hK : ∀ z, ((riemannAutocorr z : ℝ) : ℂ) = ∫ ξ, spectralChar ξ z * phiFourier ξ ^ 2 :=
    riemannAutocorr_eq_integral
  simp_rw [hK]
  have step1 : ∀ v, ∫ w, g v * conj (g w) * ∫ ξ, spectralChar ξ (y + w - v) * phiFourier ξ ^ 2 =
      ∫ ξ, g v * phiFourier ξ ^ 2 * spectralChar ξ (y - v) * conj (𝓕 g ξ) := by
    intro v
    have e1 : ∀ w, g v * conj (g w) * ∫ ξ, spectralChar ξ (y + w - v) * phiFourier ξ ^ 2 =
        ∫ ξ, g v * conj (g w) * (spectralChar ξ (y + w - v) * phiFourier ξ ^ 2) := fun w =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_integral_swap]
    · refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only
      rw [conj_fourier_eq_integral, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only
      rw [show y + w - v = (y - v) + w by ring, spectralChar_add]
      ring
    · refine (((hgi.norm.mul_prod hX.norm)).const_mul ‖g v‖).mono' ?_
        (Eventually.of_forall fun p => ?_)
      · exact (continuous_const.mul ((hg.comp continuous_fst).star)).mul
          ((continuous_spectralChar.comp (continuous_snd.prodMk
            ((continuous_const.add continuous_fst).sub continuous_const))).mul
            (hXc.comp continuous_snd)) |>.aestronglyMeasurable
      · change ‖g v * conj (g p.1) * (spectralChar p.2 (y + p.1 - v) * phiFourier p.2 ^ 2)‖ ≤
          ‖g v‖ * (‖g p.1‖ * ‖phiFourier p.2 ^ 2‖)
        rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, norm_spectralChar]
        ring_nf; rfl
  simp_rw [step1]
  rw [integral_integral_swap]
  · refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    have e : ∀ x, g x * phiFourier ξ ^ 2 * spectralChar ξ (y - x) * conj (𝓕 g ξ) =
        (phiFourier ξ ^ 2 * conj (𝓕 g ξ) * spectralChar ξ y) * (g x * spectralChar ξ (-x)) := by
      intro x; rw [show y - x = y + -x by ring, spectralChar_add]; ring
    simp_rw [e]
    rw [integral_const_mul, ← fourier_eq_integral_spectralChar]
    ring
  · refine ((hgi.norm.mul_prod (hX.norm.mul_const N))).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hg.comp continuous_fst).mul (hXc.comp continuous_snd)).mul
        (continuous_spectralChar.comp (continuous_snd.prodMk (continuous_const.sub continuous_fst)))).mul
        ((hFg.comp continuous_snd).star) |>.aestronglyMeasurable
    · change ‖g p.1 * phiFourier p.2 ^ 2 * spectralChar p.2 (y - p.1) * conj (𝓕 g p.2)‖ ≤
        ‖g p.1‖ * (‖phiFourier p.2 ^ 2‖ * N)
      rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, norm_spectralChar, mul_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (norm_fourier_le_integral_norm' g p.2) (norm_nonneg _)) (norm_nonneg _)


/-! ## The localized spectral test -/

/-- An even bump `φ(x) = S(1/4 − x²)`, positive exactly on `(−1/2, 1/2)`. -/
def localBump (x : ℝ) : ℝ := Real.smoothTransition (1 / 4 - x ^ 2)

theorem contDiff_localBump : ContDiff ℝ (⊤ : ℕ∞) localBump :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem continuous_localBump : Continuous localBump := contDiff_localBump.continuous

theorem localBump_neg (x : ℝ) : localBump (-x) = localBump x := by simp [localBump]

theorem localBump_nonneg (x : ℝ) : 0 ≤ localBump x := Real.smoothTransition.nonneg _

theorem localBump_eq_zero {x : ℝ} (h : 1 / 2 ≤ |x|) : localBump x = 0 := by
  unfold localBump
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : (1 / 2) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  rw [sq_abs] at this; linarith

theorem localBump_zero_pos : 0 < localBump 0 := by
  unfold localBump; exact Real.smoothTransition.pos_of_pos (by norm_num)

theorem hasCompactSupport_localBump_sq : HasCompactSupport fun s => localBump s ^ 2 := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => ?_
  have : 1 < |x| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (show x < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x by linarith)]; linarith
  rw [localBump_eq_zero (by linarith), zero_pow two_ne_zero]

/-- `B(x) = ∫ φ(s)² cos(2πsx) ds`. -/
def bumpCos (x : ℝ) : ℝ := ∫ s, localBump s ^ 2 * Real.cos (2 * π * s * x)

theorem integral_localBump_sq_mul_sin (x : ℝ) :
    ∫ s, localBump s ^ 2 * Real.sin (2 * π * s * x) = 0 := by
  have h := integral_neg_eq_self (fun s => localBump s ^ 2 * Real.sin (2 * π * s * x)) volume
  have e : (fun s => localBump (-s) ^ 2 * Real.sin (2 * π * -s * x)) =
      fun s => -(localBump s ^ 2 * Real.sin (2 * π * s * x)) := by
    funext s; rw [localBump_neg, show 2 * π * -s * x = -(2 * π * s * x) by ring, Real.sin_neg]; ring
  rw [e, integral_neg] at h
  linarith

/-- **The localized pairing.** For `η > 0`, `∫ φ((ξ − ξ₀)/η)² (e^{2πiξy} + e^{−2πiξy}) dξ
= 2η cos(2πξ₀y) B(ηy)`. -/
theorem integral_localBump_spectralChar {η : ℝ} (hη : 0 < η) (ξ₀ y : ℝ) :
    ∫ ξ, ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * (spectralChar ξ y + spectralChar ξ (-y)) =
      ((2 * η * Real.cos (2 * π * ξ₀ * y) * bumpCos (η * y) : ℝ) : ℂ) := by
  have hc : ∀ ξ, spectralChar ξ y + spectralChar ξ (-y) = ((2 * Real.cos (2 * π * ξ * y) : ℝ) : ℂ) := by
    intro ξ
    unfold spectralChar
    have e0 : (2 * π * ξ * -y : ℝ) = -(2 * π * ξ * y) := by ring
    rw [e0, Complex.ofReal_neg]
    set θ : ℝ := 2 * π * ξ * y
    have h2 : (2 : ℂ) * Complex.cos (θ : ℂ) =
        Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I) := by
      rw [Complex.cos]; ring
    push_cast
    rw [h2]
  simp_rw [hc]
  rw [show (fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) *
      ((2 * Real.cos (2 * π * ξ * y) : ℝ) : ℂ)) =
      fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 * (2 * Real.cos (2 * π * ξ * y)) : ℝ) : ℂ) by
    funext ξ; push_cast; ring]
  rw [integral_complex_ofReal]
  congr 1
  -- substitute `ξ = ξ₀ + η s`
  set H : ℝ → ℝ := fun s => localBump s ^ 2 * (2 * Real.cos (2 * π * (ξ₀ + η * s) * y)) with hH
  have e1 : (fun ξ => localBump ((ξ - ξ₀) / η) ^ 2 * (2 * Real.cos (2 * π * ξ * y))) =
      fun ξ => (fun t => H (t / η)) (ξ - ξ₀) := by
    funext ξ; simp only [hH]; congr 3; field_simp; ring
  rw [e1, integral_sub_right_eq_self (fun t => H (t / η)) ξ₀, Measure.integral_comp_div,
    abs_of_pos hη, smul_eq_mul]
  simp only [hH]
  have e2 : ∀ s, localBump s ^ 2 * (2 * Real.cos (2 * π * (ξ₀ + η * s) * y)) =
      2 * Real.cos (2 * π * ξ₀ * y) * (localBump s ^ 2 * Real.cos (2 * π * s * (η * y))) -
        2 * Real.sin (2 * π * ξ₀ * y) * (localBump s ^ 2 * Real.sin (2 * π * s * (η * y))) := by
    intro s
    rw [show 2 * π * (ξ₀ + η * s) * y = 2 * π * ξ₀ * y + 2 * π * s * (η * y) by ring, Real.cos_add]
    ring
  simp_rw [e2]
  have hi : ∀ f : ℝ → ℝ, Continuous f → Integrable fun s => localBump s ^ 2 * f s := fun f hf =>
    ((continuous_localBump.pow 2).mul hf).integrable_of_hasCompactSupport
      (hasCompactSupport_localBump_sq.mul_right)
  rw [integral_sub ((hi _ (by fun_prop)).const_mul _) ((hi _ (by fun_prop)).const_mul _),
    integral_const_mul, integral_const_mul, integral_localBump_sq_mul_sin, bumpCos]
  ring


theorem contDiff_phiFourier : ContDiff ℝ (⊤ : ℕ∞) phiFourier := by
  have h1 : ContDiff ℂ (⊤ : ℕ∞) XiC := XiC_differentiable.contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have h3 := (h1.restrict_scalars ℝ).comp h2
  have e : phiFourier = XiC ∘ (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) := by
    funext ξ; simp only [Function.comp, phiFourier_eq_XiC]; push_cast; ring_nf
  rw [e]; exact h3

theorem contDiff_phiFourierReal : ContDiff ℝ (⊤ : ℕ∞) phiFourierReal := by
  have e : phiFourierReal = fun ξ => (phiFourier ξ).re := by
    funext ξ; rw [phiFourier_eq_ofReal, Complex.ofReal_re]
  rw [e]; exact Complex.reCLM.contDiff.comp contDiff_phiFourier

/-- The spectral profile `u(ξ) = φ((ξ − ξ₀)/η) / X(ξ)`, real form. -/
def localProfile (η ξ₀ ξ : ℝ) : ℝ := localBump ((ξ - ξ₀) / η) * (phiFourierReal ξ)⁻¹

theorem localBump_localize_eq_zero {η ξ₀ ξ : ℝ} (hη : 0 < η) (h : η / 2 ≤ |ξ - ξ₀|) :
    localBump ((ξ - ξ₀) / η) = 0 := by
  refine localBump_eq_zero ?_
  rw [abs_div, abs_of_pos hη, le_div_iff₀ hη]; linarith

theorem contDiff_localProfile {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (localProfile η ξ₀) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x - ξ₀| < η
  · have hb : ContDiff ℝ (⊤ : ℕ∞) fun ξ => localBump ((ξ - ξ₀) / η) :=
      contDiff_localBump.comp ((contDiff_id.sub contDiff_const).div_const η)
    exact hb.contDiffAt.mul (contDiff_phiFourierReal.contDiffAt.inv (hfree x hx))
  · push Not at hx
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    have hball : ∀ᶠ ξ in 𝓝 x, |ξ - x| < η / 2 := by
      have := Metric.ball_mem_nhds x (half_pos hη)
      filter_upwards [this] with ξ hξ
      rwa [Metric.mem_ball, Real.dist_eq] at hξ
    filter_upwards [hball] with ξ hξ
    have h1 : η / 2 ≤ |ξ - ξ₀| := by
      have := abs_sub_abs_le_abs_sub (x - ξ₀) (ξ - ξ₀)
      rw [show x - ξ₀ - (ξ - ξ₀) = -(ξ - x) by ring, abs_neg] at this
      linarith
    unfold localProfile
    rw [localBump_localize_eq_zero hη h1, zero_mul]

theorem hasCompactSupport_localProfile {η : ℝ} (hη : 0 < η) (ξ₀ : ℝ) :
    HasCompactSupport (localProfile η ξ₀) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := ξ₀ - η) (b := ξ₀ + η)) fun x hx => ?_
  have h1 : η / 2 ≤ |x - ξ₀| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (show x - ξ₀ < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x - ξ₀ by linarith)]; linarith
  unfold localProfile
  rw [localBump_localize_eq_zero hη h1, zero_mul]

/-- The complex profile. -/
def localProfileC (η ξ₀ ξ : ℝ) : ℂ := (localProfile η ξ₀ ξ : ℂ)

theorem contDiff_localProfileC {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (localProfileC η ξ₀) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_localProfile hη hfree)

theorem hasCompactSupport_localProfileC {η : ℝ} (hη : 0 < η) (ξ₀ : ℝ) :
    HasCompactSupport (localProfileC η ξ₀) :=
  (hasCompactSupport_localProfile hη ξ₀).comp_left Complex.ofReal_zero

/-- `X² |u|² = φ((ξ − ξ₀)/η)²`. -/
theorem phiFourier_sq_mul_localProfileC {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (ξ : ℝ) :
    phiFourier ξ ^ 2 * (localProfileC η ξ₀ ξ * conj (localProfileC η ξ₀ ξ)) =
      ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) := by
  unfold localProfileC localProfile
  rw [phiFourier_eq_ofReal, Complex.conj_ofReal]
  by_cases hx : |ξ - ξ₀| < η
  · have hP : (phiFourierReal ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hfree ξ hx)
    push_cast
    field_simp
  · push Not at hx
    rw [localBump_localize_eq_zero hη (by linarith)]
    push_cast; ring


/-- The localized test `g = 𝓕⁻u` as a Schwartz function. -/
def localTest {η ξ₀ : ℝ} (hη : 0 < η) (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) :
    SchwartzMap ℝ ℂ :=
  𝓕⁻ ((hasCompactSupport_localProfileC hη ξ₀).toSchwartzMap (contDiff_localProfileC hη hfree))

theorem fourier_localTest {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) :
    𝓕 (localTest hη hfree : ℝ → ℂ) = localProfileC η ξ₀ := by
  rw [← SchwartzMap.fourier_coe, localTest, FourierInvPair.fourier_fourierInv_eq]
  rfl

theorem exists_localTest_decay {η ξ₀ : ℝ} (hη : 0 < η)
    (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) (m : ℕ) :
    ∃ D : ℝ, ∀ x, ‖localTest hη hfree x‖ ≤ D * ((1 + |x|) ^ m)⁻¹ := by
  set f := localTest hη hfree
  refine ⟨2 ^ m * ((Finset.Iic (m, 0)).sup fun p => SchwartzMap.seminorm ℝ p.1 p.2) f,
    fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [le_mul_inv_iff₀ (by positivity), mul_comm]
  exact h

theorem hasCompactSupport_localBump_localize_sq {η : ℝ} (hη : 0 < η) (ξ₀ : ℝ) :
    HasCompactSupport fun ξ => localBump ((ξ - ξ₀) / η) ^ 2 := by
  refine HasCompactSupport.intro (isCompact_Icc (a := ξ₀ - η) (b := ξ₀ + η)) fun x hx => ?_
  have h1 : η / 2 ≤ |x - ξ₀| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (show x - ξ₀ < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x - ξ₀ by linarith)]; linarith
  rw [localBump_localize_eq_zero hη h1, zero_pow two_ne_zero]

/-- **Positivity on zero-free windows.** If `X` has no zero within `η` of `ξ₀`, then
`Σ v(n) B(η log n) cos(2πξ₀ log n) ≥ 0`. -/
theorem localized_deviation_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {η ξ₀ : ℝ} (hη : 0 < η) (hfree : ∀ ξ, |ξ - ξ₀| < η → phiFourierReal ξ ≠ 0) :
    0 ≤ ∑' n : ℕ, normDeficit lam n * bumpCos (η * Real.log n) *
      Real.cos (2 * π * ξ₀ * Real.log n) := by
  obtain ⟨D, hD⟩ := exists_localTest_decay hη hfree (k + 2)
  set g := (localTest hη hfree : ℝ → ℂ) with hgdef
  have hg : Continuous g := SchwartzMap.continuous _
  have hgi : Integrable g := SchwartzMap.integrable _
  have h := normDeficit_pairing_nonneg_of_decay hW hA hZ hg hD
  have hbc : Continuous fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_localBump.comp
      ((continuous_id.sub continuous_const).div_const η)).pow 2)
  have hbs : HasCompactSupport fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) :=
    (hasCompactSupport_localBump_localize_sq hη ξ₀).comp_left Complex.ofReal_zero
  have hint : ∀ y, Integrable fun ξ => ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * spectralChar ξ y :=
    fun y => (hbc.mul (continuous_spectralChar.comp (continuous_id.prodMk continuous_const)))
      |>.integrable_of_hasCompactSupport hbs.mul_right
  have hpf : ∀ y, riemannPairForm riemannAutocorr g y =
      ∫ ξ, ((localBump ((ξ - ξ₀) / η) ^ 2 : ℝ) : ℂ) * spectralChar ξ y := by
    intro y
    rw [riemannPairForm_eq_integral_fourier hg hgi, hgdef, fourier_localTest]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [phiFourier_sq_mul_localProfileC hη hfree]
  have hsum : ∀ y, riemannPairForm riemannAutocorr g y + riemannPairForm riemannAutocorr g (-y) =
      ((2 * η * Real.cos (2 * π * ξ₀ * y) * bumpCos (η * y) : ℝ) : ℂ) := by
    intro y
    rw [hpf, hpf, ← integral_add (hint y) (hint (-y)), ← integral_localBump_spectralChar hη ξ₀ y]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  simp_rw [hsum] at h
  have e : (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      ((2 * η * Real.cos (2 * π * ξ₀ * Real.log n) * bumpCos (η * Real.log n) : ℝ) : ℂ)) =
      ((2 * η * ∑' n : ℕ, normDeficit lam n * bumpCos (η * Real.log n) *
        Real.cos (2 * π * ξ₀ * Real.log n) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast; ring
  rw [e, Complex.ofReal_re] at h
  have h2η : 0 < 2 * η := by linarith
  exact nonneg_of_mul_nonneg_right (by linarith) h2η |> fun h' => by
    rcases le_or_gt 0 (∑' n : ℕ, normDeficit lam n * bumpCos (η * Real.log n) *
        Real.cos (2 * π * ξ₀ * Real.log n)) with h3 | h3
    · exact h3
    · nlinarith

/-! ## The bump transform `B` -/

/-- `φ²` as a complex function. -/
def bumpSqC (s : ℝ) : ℂ := ((localBump s ^ 2 : ℝ) : ℂ)

theorem contDiff_bumpSqC : ContDiff ℝ (⊤ : ℕ∞) bumpSqC :=
  Complex.ofRealCLM.contDiff.comp (contDiff_localBump.pow 2)

theorem hasCompactSupport_bumpSqC : HasCompactSupport bumpSqC :=
  hasCompactSupport_localBump_sq.comp_left Complex.ofReal_zero

theorem integrable_localBump_sq_mul {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable fun s => localBump s ^ 2 * f s :=
  ((continuous_localBump.pow 2).mul hf).integrable_of_hasCompactSupport
    hasCompactSupport_localBump_sq.mul_right

/-- `B = Re 𝓕(φ²)`. -/
theorem bumpCos_eq_re_fourier (x : ℝ) : bumpCos x = (𝓕 bumpSqC x).re := by
  rw [fourier_apply_eq_integral_cexp, ← RCLike.re_to_complex, ← integral_re]
  · unfold bumpCos
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [bumpSqC, RCLike.re_to_complex]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  · exact ((by fun_prop : Continuous fun s : ℝ => Complex.exp (-((2 * π * s * x : ℝ) : ℂ) * I)).mul
      (Complex.continuous_ofReal.comp (continuous_localBump.pow 2))).integrable_of_hasCompactSupport
      hasCompactSupport_bumpSqC.mul_left

theorem continuous_bumpCos : Continuous bumpCos := by
  have h : bumpCos = fun x => (𝓕 bumpSqC x).re := funext bumpCos_eq_re_fourier
  rw [h]
  exact Complex.continuous_re.comp (continuous_fourier_of_integrable_real
    ((Complex.continuous_ofReal.comp (continuous_localBump.pow 2)).integrable_of_hasCompactSupport
      hasCompactSupport_bumpSqC))

theorem bumpCos_zero_pos : 0 < bumpCos 0 := by
  unfold bumpCos
  simp only [mul_zero, Real.cos_zero, mul_one]
  exact (continuous_localBump.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_localBump_sq (fun s => sq_nonneg _) (x := 0)
    (pow_ne_zero 2 localBump_zero_pos.ne')

theorem abs_bumpCos_le (x : ℝ) : |bumpCos x| ≤ bumpCos 0 := by
  unfold bumpCos
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [← Real.norm_eq_abs]
  have hi : Integrable fun s => localBump s ^ 2 := by
    simpa using integrable_localBump_sq_mul (f := fun _ => (1 : ℝ)) continuous_const
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) hi (Eventually.of_forall fun s => ?_))
  beta_reduce
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)

/-- Rapid decay of `B`. -/
theorem exists_abs_bumpCos_le (J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |bumpCos x| ≤ K * ((1 + |x|) ^ J)⁻¹ := by
  set f : SchwartzMap ℝ ℂ := 𝓕 (hasCompactSupport_bumpSqC.toSchwartzMap contDiff_bumpSqC) with hf
  set K := 2 ^ J * ((Finset.Iic (J, 0)).sup fun p => SchwartzMap.seminorm ℝ p.1 p.2) f with hK
  have hK0 : 0 ≤ K := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (J, 0)) (k := J) (n := 0)
      le_rfl le_rfl f 0
    exact le_trans (by positivity) this
  refine ⟨K, hK0, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (J, 0)) (k := J) (n := 0)
    le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hfx : f x = 𝓕 bumpSqC x := by
    rw [hf, SchwartzMap.fourier_coe]; rfl
  rw [hfx] at h
  rw [bumpCos_eq_re_fourier, le_mul_inv_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)).trans h

end

end RHTower
