import GaloisForLFunctions.RHTower.EigenPairLineConvolution
import GaloisForLFunctions.RHTower.EigenPairLineIntegrable
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap
import GaloisForLFunctions.RHTower.HedenmalmTwoEndedVolterraDefect
import GaloisForLFunctions.RHTower.ThetaCuspReflection
import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHilbert
import Mathlib.Analysis.Fourier.Inversion

/-!
# Per-frequency evaluation of the eigen-pair line product

For zeros `α, β` of `XiC` and a line height `|Y| < 1`, the line product of the removable
quotients `U_α(t - iY)·conj(U_β(t + iY))` is the Fourier transform of the convolution of the
tilted time-side eigenfunctions of `-α` and `-β`, i.e. of `e^{-Yy}·c_{-α,-β}(y)` where

`c_{α,β}(y) = ∫ u_α(x) conj(u_β(x - y)) dx`

is the time-side correlation of the theta eigenfunctions.  Fourier inversion then evaluates
every von Mangoldt frequency: on the line `Re s = 1/2 + Y`,

`∫ Λ(n) n^{-s}·U_α(t - iY) conj(U_β(t + iY)) dt = 2π Λ(n) n^{-1/2} c_{-α,-β}(-log n)`,

independently of `Y`.  At zeros the eigenfunctions are reflection-odd, `u_{-α}(-x) = -u_α(x)`,
so `c_{-α,-β}(-y) = c_{α,β}(y)`.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex FourierTransform Convolution Set

/-- The time-side correlation `c_{α,β}(y) = ∫ u_α(x) conj(u_β(x - y)) dx`. -/
def eigenPairCorrelation (α β : ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, hedenmalmCausalVolterra α x * (starRingEnd ℂ) (hedenmalmCausalVolterra β (x - y))

/-- The `-Y`-tilted flow of `α`. -/
def eigenTiltLeft (α : ℂ) (Y : ℝ) (x : ℝ) : ℂ :=
  hedenmalmCausalVolterra α x * Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ))

/-- The conjugate-reflected `Y`-tilted flow of `β`. -/
def eigenTiltRight (β : ℂ) (Y : ℝ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (hedenmalmCausalVolterra β (-x) * Complex.exp ((Y : ℂ) * ((-x : ℝ) : ℂ)))

theorem eigenTilt_convolution_eq (α β : ℂ) (Y y : ℝ) :
    (eigenTiltLeft α Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight β Y) y =
      Complex.exp (((-Y * y : ℝ)) : ℂ) * eigenPairCorrelation α β y := by
  rw [convolution_def, eigenPairCorrelation, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.mul_apply', eigenTiltLeft, eigenTiltRight, map_mul]
  have hconj : (starRingEnd ℂ) (Complex.exp ((Y : ℂ) * ((-(y - x) : ℝ) : ℂ))) =
      Complex.exp ((Y : ℂ) * ((-(y - x) : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  rw [hconj, show -(y - x) = x - y by ring]
  have hexp : Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ)) * Complex.exp ((Y : ℂ) * ((x - y : ℝ) : ℂ)) =
      Complex.exp (((-Y * y : ℝ)) : ℂ) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc hedenmalmCausalVolterra α x * Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ)) *
        ((starRingEnd ℂ) (hedenmalmCausalVolterra β (x - y)) *
          Complex.exp ((Y : ℂ) * ((x - y : ℝ) : ℂ)))
      = (Complex.exp (((-Y : ℝ) : ℂ) * (x : ℂ)) * Complex.exp ((Y : ℂ) * ((x - y : ℝ) : ℂ))) *
          (hedenmalmCausalVolterra α x * (starRingEnd ℂ) (hedenmalmCausalVolterra β (x - y))) := by
        ring
    _ = _ := by rw [hexp]

theorem integrable_eigenTiltLeft {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0) {Y : ℝ}
    (hY : |Y| < 1) : Integrable (eigenTiltLeft α Y) :=
  integrable_hedenmalm_realTilt hα h0 (by rwa [abs_neg])

theorem integrable_eigenTiltRight {β : ℂ} (hβ : |β.im| < 1) (h0 : XiC β = 0) {Y : ℝ}
    (hY : |Y| < 1) : Integrable (eigenTiltRight β Y) :=
  integrable_conj_comp (integrable_hedenmalm_realTilt hβ h0 hY).comp_neg

theorem continuous_eigenTiltRight {β : ℂ} (hβ : |β.im| < 1) (Y : ℝ) :
    Continuous (eigenTiltRight β Y) := by
  unfold eigenTiltRight
  exact Complex.continuous_conj.comp
    (((continuous_hedenmalmCausalVolterra hβ).comp continuous_neg).mul (by fun_prop))

theorem bddAbove_norm_eigenTiltRight {β : ℂ} (hβ : |β.im| < 1) (h0 : XiC β = 0) {Y : ℝ}
    (hY : |Y| < 1) : BddAbove (Set.range fun x => ‖eigenTiltRight β Y x‖) := by
  refine ⟨thetaCuspDerivativeExpConstant 0 / (1 - |β.im|), ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := norm_hedenmalmThetaEigen_mul_exp_le hβ h0 ((Y : ℂ) * Complex.I) (-x)
  have heq : ‖eigenTiltRight β Y x‖ =
      ‖hedenmalmCausalVolterra β (-x) * Complex.exp (-I * ((Y : ℂ) * Complex.I) * ((-x : ℝ) : ℂ))‖ := by
    rw [eigenTiltRight, RCLike.norm_conj]
    congr 3
    linear_combination ((Y : ℂ) * ((-x : ℝ) : ℂ)) * Complex.I_sq
  change ‖eigenTiltRight β Y x‖ ≤ _
  rw [heq]
  refine h.trans ?_
  have hK : 0 ≤ thetaCuspDerivativeExpConstant 0 / (1 - |β.im|) :=
    div_nonneg (thetaCuspDerivativeExpConstant_nonneg 0) (by linarith [hβ])
  have him : |((Y : ℂ) * Complex.I).im| = |Y| := by simp
  rw [him]
  calc thetaCuspDerivativeExpConstant 0 / (1 - |β.im|) * Real.exp (-(1 - |Y|) * |(-x)|)
      ≤ thetaCuspDerivativeExpConstant 0 / (1 - |β.im|) * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (1 - |Y|) * |(-x)| := mul_nonneg (by linarith) (abs_nonneg _)
        linarith
    _ = _ := mul_one _

/-- The convolution of the tilted flows is continuous and integrable. -/
theorem continuous_eigenTilt_convolution {α β : ℂ} (hα : |α.im| < 1) (h0α : XiC α = 0)
    (hβ : |β.im| < 1) (h0β : XiC β = 0) {Y : ℝ} (hY : |Y| < 1) :
    Continuous (eigenTiltLeft α Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight β Y) :=
  BddAbove.continuous_convolution_right_of_integrable _ (bddAbove_norm_eigenTiltRight hβ h0β hY)
    (integrable_eigenTiltLeft hα h0α hY) (continuous_eigenTiltRight hβ Y)

theorem integrable_eigenTilt_convolution {α β : ℂ} (hα : |α.im| < 1) (h0α : XiC α = 0)
    (hβ : |β.im| < 1) (h0β : XiC β = 0) {Y : ℝ} (hY : |Y| < 1) :
    Integrable (eigenTiltLeft α Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight β Y) :=
  (integrable_eigenTiltLeft hα h0α hY).integrable_convolution _
    (integrable_eigenTiltRight hβ h0β hY)

/-- **Rescaled Fourier inversion.**  For continuous integrable `h` with integrable transform,
`∫ e^{-itL} 𝓕h(t/2π) dt = 2π h(-L)`. -/
theorem integral_exp_mul_fourier_rescale {h : ℝ → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hF : Integrable (𝓕 h)) (L : ℝ) :
    ∫ t : ℝ, Complex.exp (-(t : ℂ) * (L : ℂ) * Complex.I) * 𝓕 h (t / (2 * Real.pi)) =
      (2 * Real.pi : ℝ) * h (-L) := by
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hc hi hF) (-L)
  rw [Real.fourierInv_eq'] at hinv
  set g : ℝ → ℂ := fun ξ =>
    Complex.exp (((2 * Real.pi * (ξ * (-L)) : ℝ)) * Complex.I) • 𝓕 h ξ with hg
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcomp := Measure.integral_comp_mul_left g (1 / (2 * Real.pi))
  have hlhs : (fun t : ℝ => Complex.exp (-(t : ℂ) * (L : ℂ) * Complex.I) *
      𝓕 h (t / (2 * Real.pi))) = fun t => g (1 / (2 * Real.pi) * t) := by
    funext t
    simp only [hg, smul_eq_mul]
    congr 2
    · push_cast
      field_simp
    · ring_nf
  rw [hlhs, hcomp]
  simp only [RCLike.inner_apply, conj_trivial] at hinv
  rw [show (∫ y : ℝ, g y) = h (-L) by
    rw [← hinv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hg]
    congr 3
    push_cast; ring]
  rw [one_div, inv_inv, abs_of_pos hpi, Complex.real_smul]

/-- The eigen-pair line product in quotient form, `W(t) = U_α(t - iY) conj(U_β(t + iY))`. -/
def eigenPairLine (α β : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  xiThetaEigenFourier α ((t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I) *
    (starRingEnd ℂ) (xiThetaEigenFourier β ((t : ℂ) + (Y : ℂ) * Complex.I))

/-- The quotient line product is the transform line product of the negated zeros. -/
theorem eigenPairLine_eq_fourier {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) {Y : ℝ}
    (hY : |Y| < 1) (hYα : (1 / 2 : ℝ) ≤ |Y|) (t : ℝ) :
    eigenPairLine α β Y t =
      𝓕 (eigenTiltLeft (-α) Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight (-β) Y)
        (t / (2 * Real.pi)) := by
  have hαh := abs_im_lt_half_of_XiC_eq_zero hα
  have hβh := abs_im_lt_half_of_XiC_eq_zero hβ
  have hnα : |(-α).im| < 1 := by rw [Complex.neg_im, abs_neg]; linarith
  have hnβ : |(-β).im| < 1 := by rw [Complex.neg_im, abs_neg]; linarith
  have h0nα : XiC (-α) = 0 := by rw [XiC_even, hα]
  have h0nβ : XiC (-β) = 0 := by rw [XiC_even, hβ]
  have h : hedenmalmThetaEigenTransform (-α) ((t : ℂ) - (Y : ℂ) * Complex.I) *
      (starRingEnd ℂ) (hedenmalmThetaEigenTransform (-β) ((t : ℂ) + (Y : ℂ) * Complex.I)) =
      𝓕 (eigenTiltLeft (-α) Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight (-β) Y)
        (t / (2 * Real.pi)) :=
    transform_pair_line_eq_fourier_convolution hnα h0nα hnβ h0nβ hY t
  have hz1 : |((t : ℂ) - (Y : ℂ) * Complex.I).im| < 1 := by simpa using hY
  have hz2 : |((t : ℂ) + (Y : ℂ) * Complex.I).im| < 1 := by simpa using hY
  have hne1 : (t : ℂ) - (Y : ℂ) * Complex.I ≠ -(-α) := by
    intro he
    have := congrArg Complex.im he
    simp at this
    rw [← this] at hαh
    rw [abs_neg] at hαh
    linarith
  have hne2 : (t : ℂ) + (Y : ℂ) * Complex.I ≠ -(-β) := by
    intro he
    have := congrArg Complex.im he
    simp at this
    rw [← this] at hβh
    linarith
  rw [hedenmalmThetaEigenTransform_eq_xiThetaEigenFourier hnα h0nα hz1 hne1,
    hedenmalmThetaEigenTransform_eq_xiThetaEigenFourier hnβ h0nβ hz2 hne2, neg_neg, neg_neg] at h
  rw [eigenPairLine, ← h]
  have hpt : (t : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I = (t : ℂ) - (Y : ℂ) * Complex.I := by
    push_cast; ring
  rw [hpt, map_mul, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Per-frequency evaluation.**  On the line `Re s = 1/2 + Y`, the `n`-th von Mangoldt term of
the line product is `2π Λ(n) n^{-1/2} c_{-α,-β}(-log n)`. -/
theorem integral_vonMangoldt_term_mul_eigenPairLine {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0)
    {Y : ℝ} (hY : |Y| < 1) (hYα : (1 / 2 : ℝ) ≤ |Y|) (n : ℕ) :
    ∫ t : ℝ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((1 / 2 + Y : ℝ) : ℂ) + t * I) n * eigenPairLine α β Y t =
      2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        eigenPairCorrelation (-α) (-β) (-Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  have hn0 : n ≠ 0 := hn.ne'
  have hαh := abs_im_lt_half_of_XiC_eq_zero hα
  have hβh := abs_im_lt_half_of_XiC_eq_zero hβ
  have hnα : |(-α).im| < 1 := by rw [Complex.neg_im, abs_neg]; linarith
  have hnβ : |(-β).im| < 1 := by rw [Complex.neg_im, abs_neg]; linarith
  have h0nα : XiC (-α) = 0 := by rw [XiC_even, hα]
  have h0nβ : XiC (-β) = 0 := by rw [XiC_even, hβ]
  set h := eigenTiltLeft (-α) Y ⋆[ContinuousLinearMap.mul ℂ ℂ] eigenTiltRight (-β) Y with hh
  have hc := continuous_eigenTilt_convolution hnα h0nα hnβ h0nβ hY
  have hi := integrable_eigenTilt_convolution hnα h0nα hnβ h0nβ hY
  have hW : Integrable (eigenPairLine α β Y) := by
    have := integrable_eigenPair_line hα hβ (A := |Y|) (δ := 1/4) (abs_nonneg _) hY
      (by norm_num) (by linarith [Real.pi_gt_three]) le_rfl
    exact this
  have hF : Integrable (𝓕 h) := by
    refine (hW.comp_mul_left' (by positivity : (2 * Real.pi) ≠ 0)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    show eigenPairLine α β Y ((2 * Real.pi) * ξ) = 𝓕 h ξ
    rw [eigenPairLine_eq_fourier hα hβ hY hYα, hh]
    field_simp
  have hterm : ∀ t : ℝ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (((1 / 2 + Y : ℝ) : ℂ) + t * I) n * eigenPairLine α β Y t =
      ((ArithmeticFunction.vonMangoldt n : ℂ) * (((n : ℝ) ^ (-(1 / 2 + Y)) : ℝ) : ℂ)) *
        (Complex.exp (-(t : ℂ) * ((Real.log n : ℝ) : ℂ) * Complex.I) *
          𝓕 h (t / (2 * Real.pi))) := by
    intro t
    rw [LSeries.term_of_ne_zero hn0, eigenPairLine_eq_fourier hα hβ hY hYα, div_eq_mul_inv,
      ← Complex.cpow_neg]
    have hpow := natCast_cpow_neg_line_eq n hn0 (1 / 2 + Y) t
    rw [show (-(((1 / 2 + Y : ℝ) : ℂ) + t * I)) = -((1 / 2 + Y : ℝ) + t * I) by push_cast; ring,
      hpow]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hlog]
    have hreal : (((n : ℝ) ^ (-(1 / 2 + Y)) : ℝ) : ℂ) =
        Complex.exp (((Real.log n : ℝ) : ℂ) * (-((1 / 2 + Y : ℝ) : ℂ))) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
      push_cast; ring_nf
    rw [hreal, show ((Real.log n : ℝ) : ℂ) * -(((1 / 2 + Y : ℝ) : ℂ) + (t : ℂ) * I) =
        ((Real.log n : ℝ) : ℂ) * (-((1 / 2 + Y : ℝ) : ℂ)) +
          (-(t : ℂ) * ((Real.log n : ℝ) : ℂ) * Complex.I) by ring, Complex.exp_add]
    ring
  simp_rw [hterm]
  rw [integral_const_mul, integral_exp_mul_fourier_rescale hc hi hF, eigenTilt_convolution_eq]
  have hpow : ((n : ℝ) ^ (-(1 / 2 + Y)) : ℝ) * Real.exp (-Y * -Real.log n) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show -Y * -Real.log n = Real.log n * Y by ring, Real.exp_mul,
      Real.exp_log (by exact_mod_cast hn), ← Real.rpow_add (by exact_mod_cast hn)]
    congr 1; ring
  rw [← Complex.ofReal_exp]
  calc (ArithmeticFunction.vonMangoldt n : ℂ) * (((n : ℝ) ^ (-(1 / 2 + Y)) : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) * (((Real.exp (-Y * -Real.log n) : ℝ) : ℂ) *
          eigenPairCorrelation (-α) (-β) (-Real.log n)))
      = 2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((((n : ℝ) ^ (-(1 / 2 + Y)) * Real.exp (-Y * -Real.log n) : ℝ)) : ℂ) *
          eigenPairCorrelation (-α) (-β) (-Real.log n) := by push_cast; ring
    _ = _ := by rw [hpow]

/-! ## Reflection symmetry of the eigenfunctions -/

/-- At a zero, the eigenfunction of the negated zero is the negated reflection:
`u_{-α}(-x) = -u_α(x)`. -/
theorem hedenmalmCausalVolterra_neg_reflect {α : ℂ} (hα : |α.im| < 1) (h0 : XiC α = 0) (x : ℝ) :
    hedenmalmCausalVolterra (-α) (-x) = -hedenmalmCausalVolterra α x := by
  have hanti := (hedenmalmCausalVolterra_eq_antiCausal_iff hα).2 h0 x
  rw [hanti, hedenmalmCausalVolterra, hedenmalmAntiCausalVolterra]
  have hsub : (∫ t in Iic (-x), hedenmalmVolterraIntegrand (-α) (-x) t) =
      ∫ t in Ici x, hedenmalmVolterraIntegrand α x t := by
    rw [show (∫ t in Iic (-x), hedenmalmVolterraIntegrand (-α) (-x) t) =
        ∫ t in Iic (-x), hedenmalmVolterraIntegrand α x (-t) from
      setIntegral_congr_fun measurableSet_Iic fun t _ => by
        simp only [hedenmalmVolterraIntegrand, thetaCuspFullSource_neg]
        congr 2
        push_cast; ring]
    rw [integral_comp_neg_Iic, neg_neg, integral_Ici_eq_integral_Ioi]
  rw [hsub]
  ring

/-- **Reflection of the correlation**: `c_{-α,-β}(-y) = c_{α,β}(y)`. -/
theorem eigenPairCorrelation_neg_neg {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) (y : ℝ) :
    eigenPairCorrelation (-α) (-β) (-y) = eigenPairCorrelation α β y := by
  have hαi : |α.im| < 1 := by linarith [abs_im_lt_half_of_XiC_eq_zero hα]
  have hβi : |β.im| < 1 := by linarith [abs_im_lt_half_of_XiC_eq_zero hβ]
  rw [eigenPairCorrelation, eigenPairCorrelation,
    ← integral_neg_eq_self (fun x => hedenmalmCausalVolterra (-α) x *
      (starRingEnd ℂ) (hedenmalmCausalVolterra (-β) (x - -y))) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show -x - -y = -(x - y) by ring, hedenmalmCausalVolterra_neg_reflect hαi hα,
    hedenmalmCausalVolterra_neg_reflect hβi hβ, map_neg]
  ring

end

end RHTower
