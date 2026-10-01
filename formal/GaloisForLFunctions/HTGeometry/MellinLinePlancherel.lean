import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Mellin–Plancherel on a vertical line

For `Ψ` integrable and square integrable on the line `Re s = σ`,
`∫₀^∞ |Mellin⁻¹_σ Ψ (x)|² x^{2σ-1} dx = (1/2π) ∫ |Ψ(σ + it)|² dt`.

Proof: `Mellin⁻¹_σ Ψ (x) = x^{-σ} 𝓕⁻φ(-log x)` with `φ(y) = Ψ(σ + 2πiy)`; the substitution
`x = e^{-u}` turns the weighted integral into `∫ |𝓕⁻φ|²`, and Plancherel for integrable `L²`
functions (`‖𝓕u‖ = ‖u‖` on `L²` together with the Fourier integral of an integrable
representative) gives `∫ |φ|²`.
-/

open MeasureTheory Set Filter Complex
open scoped FourierTransform ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `‖f‖² = ∫ |f|²` for `f ∈ L²`. -/
theorem Lp_two_norm_sq_eq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ a, ‖(f : ℝ → ℂ) a‖ ^ 2 ∂μ := by
  have h1 : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [MeasureTheory.L2.inner_def] at h1
  have h2 : ∫ a, inner ℂ ((f : ℝ → ℂ) a) ((f : ℝ → ℂ) a) ∂μ
      = ((∫ a, ‖(f : ℝ → ℂ) a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext a
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2] at h1
  exact_mod_cast h1.symm

/-- **Plancherel for integrable `L²` functions:** `∫ |𝓕φ|² = ∫ |φ|²`. -/
theorem integral_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    ∫ ξ, ‖𝓕 φ ξ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := by
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφ2.toLp φ with hu
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] φ := hφ2.coeFn_toLp
  have hint : Integrable (u : ℝ → ℂ) := hφ.congr hcoe.symm
  have hF : ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
    refine (coeFn_fourierTransform_eq_fourierIntegral u hint).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have h1 := Lp_two_norm_sq_eq_integral (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))
  have h2 := Lp_two_norm_sq_eq_integral u
  rw [Lp.norm_fourier_eq, h2] at h1
  have e1 : ∫ ξ, ‖𝓕 φ ξ‖ ^ 2 = ∫ ξ, ‖((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hF] with ξ h; rw [h]
  have e2 : ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x h; rw [h]
  rw [e1, ← h1, e2]

/-- Substitution `x = e^{-u}`: `∫_{(0,∞)} G(-log x) x⁻¹ dx = ∫_ℝ G(u) du`. -/
theorem integral_Ioi_comp_neg_log_div (G : ℝ → ℝ) :
    ∫ x in Ioi (0 : ℝ), G (-Real.log x) * x⁻¹ = ∫ u, G u := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-x)) univ x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    rw [mul_neg_one] at h1
    exact h1.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ h
    simpa using Real.exp_injective h
  have himage : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
    rw [Set.image_univ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩; exact Real.exp_pos _
    · intro hx; exact ⟨-Real.log x, by simp [Real.exp_log hx]⟩
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun x : ℝ => G (-Real.log x) * x⁻¹)
  rw [himage] at h
  rw [h, setIntegral_univ]
  congr 1; funext u
  simp only [smul_eq_mul, Real.log_exp, neg_neg, abs_neg, abs_of_pos (Real.exp_pos _)]
  have := Real.exp_pos (-u)
  field_simp

/-- **Mellin–Plancherel on a vertical line.** If `t ↦ Ψ(σ + it)` is integrable and square
integrable, then `∫₀^∞ |Mellin⁻¹_σ Ψ (x)|² x^{2σ-1} dx = (1/2π) ∫ |Ψ(σ + it)|² dt`. -/
theorem integral_norm_sq_mellinInv {Ψ : ℂ → ℂ} {σ : ℝ}
    (hint : Integrable fun t : ℝ => Ψ ((σ : ℂ) + t * I))
    (hL2 : MemLp (fun t : ℝ => Ψ ((σ : ℂ) + t * I)) 2) :
    ∫ x in Ioi (0 : ℝ), ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖Ψ ((σ : ℂ) + t * I)‖ ^ 2 := by
  set φ : ℝ → ℂ := fun y => Ψ ((σ : ℂ) + 2 * Real.pi * y * I) with hφ
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hφeq : φ = fun y : ℝ => (fun t : ℝ => Ψ ((σ : ℂ) + t * I)) (2 * Real.pi * y) := by
    funext y; simp only [hφ]; push_cast; ring_nf
  have hφint : Integrable φ := by
    rw [hφeq]; exact hint.comp_mul_left' h2π.ne'
  have hφL2 : MemLp φ 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφint.aestronglyMeasurable]
    have h := (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).mp hL2
    rw [hφeq]
    exact h.comp_mul_left' h2π.ne'
  -- rewrite the integrand on `(0,∞)`
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1)
      = ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * x⁻¹ := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    rw [mellinInv_eq_fourierInv σ Ψ hx', norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx']
    simp only [neg_re, ofReal_re]
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
    have : x ^ ((-σ) * ((2 : ℕ) : ℝ)) * x ^ (2 * σ - 1) = x⁻¹ := by
      rw [← Real.rpow_add hx', ← Real.rpow_neg_one]
      congr 1; push_cast; ring
    calc x ^ (-σ * ((2 : ℕ) : ℝ)) * ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * x ^ (2 * σ - 1)
        = ‖𝓕⁻ φ (-Real.log x)‖ ^ 2 * (x ^ (-σ * ((2 : ℕ) : ℝ)) * x ^ (2 * σ - 1)) := by ring
      _ = _ := by rw [this]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_Ioi_comp_neg_log_div (fun u => ‖𝓕⁻ φ u‖ ^ 2)]
  have hneg : ∫ u : ℝ, ‖𝓕⁻ φ u‖ ^ 2 = ∫ u : ℝ, ‖𝓕 φ u‖ ^ 2 := by
    simp_rw [Real.fourierInv_eq_fourier_neg]
    exact integral_neg_eq_self (fun u => ‖𝓕 φ u‖ ^ 2) volume
  rw [hneg, integral_norm_sq_fourier hφint hφL2]
  have hscale : ∫ y : ℝ, ‖φ y‖ ^ 2 = ∫ y : ℝ, (fun t : ℝ => ‖Ψ ((σ : ℂ) + t * I)‖ ^ 2) (2 * Real.pi * y) := by
    congr 1; funext y; simp only [hφ]; push_cast; ring_nf
  have hsc := Measure.integral_comp_mul_left (fun t : ℝ => ‖Ψ ((σ : ℂ) + t * I)‖ ^ 2) (2 * Real.pi)
  rw [hscale, hsc, abs_inv, abs_of_pos h2π, smul_eq_mul]
  ring

end GaloisForLFunctions.HTGeometry


