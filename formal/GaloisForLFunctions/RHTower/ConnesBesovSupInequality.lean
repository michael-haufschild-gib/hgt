import GaloisForLFunctions.RHTower.ConnesFracSymbolArch

/-!
# §VII (41): the Besov–Fourier inequality

§VII (41) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `Sup_x |F(η)(x) · Sup_S |x_v|^α| ≤ c_α ∑_S ‖C_{α,v} * η‖₁`.

At the archimedean place this is proved here in the quantitative, hypothesis-free form

  `(2 C_α (2π|x|)^α − 2·(2δ^{-α}/α)) · ‖F(η)(x)‖ ≤ ‖C_{α,v} * η‖₁`   for every `x ≠ 0`,

by combining three closed results: the exchange of order in (39)
(`ConnesFracConvSwap.connes_fracConv_swap`), the multiplier identity
`F(C_{α,v}*η) = m_α · F(η)` proved here, and the growth of the symbol
(`ConnesFracSymbolArch.connes_fracSymbol_norm_lower`).  The last of these is the step Connes
states without proof.
-/

open MeasureTheory Real Set
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The Fourier character in the form mathlib's real Fourier integral uses. -/
def connesFourierChar (x y : ℝ) : ℂ := Complex.exp (((-2 * π * y * x : ℝ) : ℂ) * Complex.I)

theorem connesFourierChar_continuous (x : ℝ) : Continuous (connesFourierChar x) := by
  unfold connesFourierChar
  fun_prop

theorem norm_connesFourierChar (x y : ℝ) : ‖connesFourierChar x y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Mathlib's real Fourier integral, written as a plain product integral. -/
theorem connes_fourier_eq_integral (f : ℝ → ℂ) (x : ℝ) :
    𝓕 f x = ∫ y : ℝ, connesFourierChar x y * f y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, connesFourierChar]

theorem connes_integrable_char_mul (η : 𝓢(ℝ, ℂ)) (x ε : ℝ) :
    Integrable (fun y : ℝ => connesFourierChar x y * η (y + ε)) volume := by
  have hmaj : Integrable (fun y : ℝ => ‖(η : 𝓢(ℝ, ℂ)) (y + ε)‖) volume :=
    ((η.integrable).comp_add_right ε).norm
  refine MeasureTheory.Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (((connesFourierChar_continuous x).mul
      (η.continuous.comp (continuous_id.add continuous_const)))).aestronglyMeasurable
  · rw [norm_mul, norm_connesFourierChar, one_mul]

/-- **The symbol of the first difference.**  Translating by `ε` multiplies the transform by
`e^{2πiεx}`, so the first difference has Fourier symbol `e^{2πiεx} − 1`. -/
theorem connes_fourier_translate_diff (η : 𝓢(ℝ, ℂ)) (x ε : ℝ) :
    (∫ y : ℝ, connesFourierChar x y * (η (y + ε) - η y))
      = (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1) * 𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
      := by
  have h1 : Integrable (fun y : ℝ => connesFourierChar x y * η (y + ε)) volume :=
    connes_integrable_char_mul η x ε
  have h2 : Integrable (fun y : ℝ => connesFourierChar x y * η y) volume := by
    have h := connes_integrable_char_mul η x 0
    exact h.congr (Filter.Eventually.of_forall fun y => by simp only [add_zero])
  have hsplit : (∫ y : ℝ, connesFourierChar x y * (η (y + ε) - η y))
      = (∫ y : ℝ, connesFourierChar x y * η (y + ε))
        - ∫ y : ℝ, connesFourierChar x y * η y := by
    rw [← MeasureTheory.integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hshift : (∫ y : ℝ, connesFourierChar x y * η (y + ε))
      = Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) *
        ∫ z : ℝ, connesFourierChar x z * η z := by
    have hcomp := MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure ℝ)) (fun z : ℝ => connesFourierChar x (z - ε) * η z) ε
    have hlhs : (fun y : ℝ => (fun z : ℝ => connesFourierChar x (z - ε) * η z) (y + ε))
        = fun y : ℝ => connesFourierChar x y * η (y + ε) := by
      funext y
      simp only [add_sub_cancel_right]
    rw [hlhs] at hcomp
    rw [hcomp, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hchar : connesFourierChar x (z - ε)
        = Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) * connesFourierChar x z := by
      unfold connesFourierChar
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    show connesFourierChar x (z - ε) * η z
      = Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) * (connesFourierChar x z * η z)
    rw [hchar]
    ring
  rw [hsplit, hshift, connes_fourier_eq_integral]
  ring

/-- **The multiplier identity.**  `F(C_{α,v} * η) = m_α · F(η)`. -/
theorem connes_fourier_fracConv {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0) (η : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      = connesFracSymbol α ψ x * 𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
  have hswap := connes_fracConv_swap hα0 hα1 hψc hψ0 hψ1 hψsupp η
    (u := connesFourierChar x) (connesFourierChar_continuous x).measurable
    (fun y => le_of_eq (norm_connesFourierChar x y))
  rw [connes_fourier_eq_integral, hswap]
  have hpt : ∀ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (∫ y : ℝ, connesFourierChar x y * (η (y + ε) - η y))
      = (((connesFracWeight α ψ ε : ℝ) : ℂ) *
          (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1)) *
        𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
    intro ε
    rw [connes_fourier_translate_diff η x ε]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_mul_const, connesFracSymbol]

/-- **§VII (41) at the archimedean place.**  The `L¹` norm of `C_{α,v} * η` controls
`|x|^α ‖F(η)(x)‖`. -/
theorem connes_besov_sup_inequality {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hα2 : α < 2)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0)
    {δ : ℝ} (hδ : 0 < δ) (hψδ : ∀ s ∈ Ioc (0 : ℝ) δ, ψ s = 1)
    (η : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    (2 * (connesLevyConstant α * (2 * π * |x|) ^ α) - 2 * (2 * δ ^ (-α) / α)) *
        ‖𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ ∫ y : ℝ, ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ := by
  have hid := connes_fourier_fracConv hα0 hα1 hψc hψ0 hψ1 hψsupp η x
  have hsym := connes_fracSymbol_norm_lower hα0 hα1 hα2 hψc hψ0 hψ1 hψsupp hδ hψδ hx
  have hbd : ‖𝓕 (connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖
      ≤ ∫ y : ℝ, ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [hid, norm_mul] at hbd
  calc (2 * (connesLevyConstant α * (2 * π * |x|) ^ α) - 2 * (2 * δ ^ (-α) / α)) *
        ‖𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ ‖connesFracSymbol α ψ x‖ * ‖𝓕 ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ :=
        mul_le_mul_of_nonneg_right hsym (norm_nonneg _)
    _ ≤ ∫ y : ℝ, ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ := hbd

end

end GaloisForLFunctions.RHTower
