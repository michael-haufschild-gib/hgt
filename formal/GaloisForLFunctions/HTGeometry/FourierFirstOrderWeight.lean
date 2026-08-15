import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The first-order Fourier weight is the derivative

Multiplying the Fourier transform by the frequency is, up to the fixed factor `2π`, the Fourier
transform of the derivative:

`‖ξ · 𝓕v(ξ)‖ = (2π)⁻¹ ‖𝓕(v')(ξ)‖`.

Hence the first-order weight `1 + |ξ|` applied to `𝓕v` is dominated by the transforms of `v` and
`v'` separately, and a profile whose value and derivative are both square integrable transports to a
Fourier profile with square-integrable first-order weight.  That is exactly the hypothesis under
which a symbol of at most linear growth acts boundedly: the growth of the symbol is paid for by one
derivative, no more.
-/

open MeasureTheory Real
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The Fourier transform of an integrable profile is continuous. -/
theorem continuous_fourier {v : ℝ → X} (hv : Integrable v) : Continuous (𝓕 v) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ (E := ℝ)).continuous₂ hv

/-- **The frequency weight is the derivative.**  Multiplying by the frequency scales the transform
of the derivative by the fixed factor `2π`. -/
theorem norm_freq_smul_fourier_eq {v : ℝ → X} (hv : Integrable v) (hv' : Differentiable ℝ v)
    (hdv : Integrable (deriv v)) (ξ : ℝ) :
    |ξ| * ‖𝓕 v ξ‖ = (2 * π)⁻¹ * ‖𝓕 (deriv v) ξ‖ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  rw [Real.fourier_deriv hv hv' hdv]
  rw [norm_smul]
  have hcoef : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hcoef]
  field_simp

/-- **The first-order weight is dominated by the value and the derivative.** -/
theorem norm_firstOrder_smul_fourier_le {v : ℝ → X} (hv : Integrable v) (hv' : Differentiable ℝ v)
    (hdv : Integrable (deriv v)) (ξ : ℝ) :
    ‖(((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ‖ ≤ ‖𝓕 v ξ‖ + (2 * π)⁻¹ * ‖𝓕 (deriv v) ξ‖ := by
  have hkey := norm_freq_smul_fourier_eq hv hv' hdv ξ
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |ξ|)]
  rw [add_mul, one_mul, hkey]

/-! ## The `L²` consequence -/

/-- **A profile with square-integrable value and derivative has a square-integrable first-order
Fourier weight.**  This is the hypothesis under which a symbol of at most linear growth acts, so a
jump multiplier bounded by `1 + |ξ|` sends such a profile to `L²`. -/
theorem lintegral_sq_firstOrder_fourier_ne_top {v : ℝ → X} (hv : Integrable v)
    (hv' : Differentiable ℝ v) (hdv : Integrable (deriv v))
    (h1 : (∫⁻ ξ, ‖𝓕 v ξ‖ₑ ^ 2) ≠ ⊤) (h2 : (∫⁻ ξ, ‖𝓕 (deriv v) ξ‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ ξ, ‖(((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ‖ₑ ^ 2) ≠ ⊤ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hmaj : ∀ ξ : ℝ, ‖(((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ‖ₑ ^ 2
      ≤ 4 * (‖𝓕 v ξ‖ₑ ^ 2 + ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ‖𝓕 (deriv v) ξ‖ₑ ^ 2) := by
    intro ξ
    have hbound := norm_firstOrder_smul_fourier_le hv hv' hdv ξ
    have henorm : ‖(((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ‖ₑ
        ≤ ‖𝓕 v ξ‖ₑ + ENNReal.ofReal (2 * π)⁻¹ * ‖𝓕 (deriv v) ξ‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (norm_nonneg _)
          (by positivity)]
      exact ENNReal.ofReal_le_ofReal hbound
    have hsq : ‖(((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ‖ₑ ^ 2
        ≤ (‖𝓕 v ξ‖ₑ + ENNReal.ofReal (2 * π)⁻¹ * ‖𝓕 (deriv v) ξ‖ₑ) ^ 2 :=
      pow_le_pow_left' henorm 2
    refine hsq.trans ?_
    have hadd : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
      intro a b
      have h1 : a + b ≤ 2 * max a b :=
        (add_le_add (le_max_left a b) (le_max_right a b)).trans (by rw [two_mul])
      have h2 : max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
        rcases max_choice a b with h | h <;> rw [h]
        · exact le_self_add
        · exact le_add_self
      calc (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' h1 2
        _ = 4 * max a b ^ 2 := by ring
        _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2
    refine (hadd _ _).trans (le_of_eq ?_)
    congr 2
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity)]
  have hmeas1 : Measurable fun ξ : ℝ => ‖𝓕 v ξ‖ₑ ^ 2 :=
    ((continuous_fourier hv).enorm.measurable).pow_const 2
  have hmeas2 : Measurable fun ξ : ℝ =>
      ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ‖𝓕 (deriv v) ξ‖ₑ ^ 2 :=
    (((continuous_fourier hdv).enorm.measurable).pow_const 2).const_mul _
  have hfin : (∫⁻ ξ : ℝ, 4 * (‖𝓕 v ξ‖ₑ ^ 2
      + ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ‖𝓕 (deriv v) ξ‖ₑ ^ 2)) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)]
    refine ENNReal.mul_ne_top (by simp) ?_
    rw [lintegral_add_left hmeas1]
    refine ENNReal.add_ne_top.mpr ⟨h1, ?_⟩
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2
  exact ne_top_of_le_ne_top hfin (lintegral_mono hmaj)

/-! ## The `L²` seminorm form -/

omit [NormedSpace ℂ X] in
/-- Finiteness of the `L²` seminorm is finiteness of the squared mass. -/
theorem eLpNorm_two_ne_top_iff {f : ℝ → X} :
    eLpNorm f 2 volume ≠ ⊤ ↔ (∫⁻ ξ, ‖f ξ‖ₑ ^ 2) ≠ ⊤ := by
  have hform : eLpNorm f 2 volume = (∫⁻ ξ, ‖f ξ‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  rw [hform]
  constructor
  · intro h hc
    exact h (by rw [hc, ENNReal.top_rpow_of_pos (by norm_num)])
  · intro h hc
    exact h ((ENNReal.rpow_eq_top_iff_of_pos (by norm_num)).mp hc)

/-- **The first-order Fourier weight in `L²` seminorm form.** -/
theorem eLpNorm_firstOrder_fourier_ne_top {v : ℝ → X} (hv : Integrable v)
    (hv' : Differentiable ℝ v) (hdv : Integrable (deriv v))
    (h1 : eLpNorm (𝓕 v) 2 volume ≠ ⊤) (h2 : eLpNorm (𝓕 (deriv v)) 2 volume ≠ ⊤) :
    eLpNorm (fun ξ => (((1 + |ξ| : ℝ)) : ℂ) • 𝓕 v ξ) 2 volume ≠ ⊤ :=
  eLpNorm_two_ne_top_iff.mpr
    (lintegral_sq_firstOrder_fourier_ne_top hv hv' hdv
      (eLpNorm_two_ne_top_iff.mp h1) (eLpNorm_two_ne_top_iff.mp h2))

end GaloisForLFunctions.HTGeometry
