import GaloisForLFunctions.RHTower.DeningerCapSchwartz
import GaloisForLFunctions.RHTower.DeningerPoissonReverseMellin
import GaloisForLFunctions.RHTower.DeningerCapMellinLeft

/-!
# Mellin inversion on a vertical line

The Mellin transform of a member of Meyer's space converges and is integrable on every vertical
line to the right of `−1`, so Mellin inversion holds there and gives the pointwise bound

`‖f x‖ ≤ (2π)⁻¹ x^{-σ} ∫ ‖M(f)(σ+iy)‖ dy`.

The same works for a Poisson sum, whose logarithmic weights are the reflected Schwartz weights
already built.  Feeding the two line estimates for `1/ζ` into the bound turns the Poisson sum into
control of `f`: decay of order `x^{-2}` at infinity from the line `Re s = 2`, and a factor `x` at
the origin from the line `Re s = −1`.

* `verticalIntegrable_mellin_poisson` : the Poisson transform is integrable on the line.
* `norm_le_mellin_line` : **the inversion bound.**
* `norm_le_of_poisson_right`, `norm_le_of_poisson_left` : **`f` controlled by `Zf` at both ends.**
-/

open scoped Real SchwartzMap ContDiff FourierTransform
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The reflected Poisson weight -/

/-- The reflection of a Schwartz map. -/
def deningerReflect (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) g

@[simp] theorem deningerReflect_apply (g : 𝓢(ℝ, ℂ)) (u : ℝ) :
    deningerReflect g u = g (-u) := rfl

/-- **On a vertical line the Mellin transform of a Poisson sum is the Fourier transform of the
reflected logarithmic weight.** -/
theorem mellin_deningerPoissonValue_eq_fourier (s : ℤ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap)
    (y : ℝ) :
    mellin (deningerPoissonValue f) (((s : ℝ) : ℂ) + y * I)
      = 𝓕 ((deningerReflect (deningerPoissonSchwartz s f hf) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        (y / (2 * π)) := by
  have hre : (((s : ℝ) : ℂ) + (y : ℂ) * I).re = (s : ℝ) := by simp
  have him : (((s : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
  have hfunw : (fun u : ℝ => (Real.exp (-(s : ℝ) * u)) • deningerPoissonValue f (Real.exp (-u)))
      = ((deningerReflect (deningerPoissonSchwartz s f hf) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext u
    have harg : (-(s : ℝ) * u) = (s : ℝ) * (-u) := by ring
    show (Real.exp (-(s : ℝ) * u)) • deningerPoissonValue f (Real.exp (-u))
      = deningerPoissonWeight s f (-u)
    rw [deningerPoissonWeight, deningerExpWeight, deningerPoissonLog_eq, Complex.real_smul,
      harg]
  rw [mellin_eq_fourier, hre, him, hfunw]

/-- **The Mellin transform of a Poisson sum is integrable on every vertical line.** -/
theorem verticalIntegrable_mellin_poisson (s : ℤ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    Complex.VerticalIntegrable (mellin (deningerPoissonValue f)) (s : ℝ) := by
  set g : 𝓢(ℝ, ℂ) := deningerReflect (deningerPoissonSchwartz s f hf) with hg
  have hfun : (fun y : ℝ => mellin (deningerPoissonValue f) ((s : ℝ) + y * I))
      = fun y : ℝ => 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (y / (2 * π)) :=
    funext fun y => mellin_deningerPoissonValue_eq_fourier s f hf y
  have hschwartz : Integrable (fun z : ℝ => 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z) := by
    have hcoe : 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourier_coe _).symm
    rw [hcoe]
    exact (𝓕 g : 𝓢(ℝ, ℂ)).integrable
  have hne : (2 * π) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hscale : Integrable (fun y : ℝ => 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (y / (2 * π))) := by
    have hcomp := hschwartz.comp_mul_left' (R := (2 * π)⁻¹) (inv_ne_zero hne)
    refine hcomp.congr ?_
    filter_upwards with y
    field_simp
  show Integrable (fun y : ℝ => mellin (deningerPoissonValue f) ((s : ℝ) + y * I))
  rw [hfun]
  exact hscale

/-! ## The inversion bound -/

theorem norm_mellinInv_le (σ : ℝ) (F : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv σ F x‖ ≤ (1 / (2 * π)) * x ^ (-σ) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖ := by
  have hpi : (0 : ℝ) < 2 * π := by
    have := Real.pi_pos
    positivity
  have hnorm : ∀ y : ℝ, ‖(x : ℂ) ^ (-((σ : ℂ) + y * I)) • F ((σ : ℂ) + y * I)‖
      = x ^ (-σ) * ‖F ((σ : ℂ) + y * I)‖ := by
    intro y
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 2
    simp
  have hle : ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • F ((σ : ℂ) + y * I)‖
      ≤ ∫ y : ℝ, x ^ (-σ) * ‖F ((σ : ℂ) + y * I)‖ := by
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
  have hval : (∫ y : ℝ, x ^ (-σ) * ‖F ((σ : ℂ) + y * I)‖)
      = x ^ (-σ) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖ := by
    rw [integral_const_mul]
  rw [mellinInv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  calc (1 / (2 * π)) * ‖∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) • F ((σ : ℂ) + y * I)‖
      ≤ (1 / (2 * π)) * (x ^ (-σ) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hval]
        exact hle
    _ = (1 / (2 * π)) * x ^ (-σ) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖ := by ring

/-- **The inversion bound for a member of Meyer's space.** -/
theorem norm_le_mellin_line (s : ℤ) (hs : -1 ≤ s) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap)
    {x : ℝ} (hx : 0 < x) :
    ‖f x‖ ≤ (1 / (2 * π)) * x ^ (-(s : ℝ))
      * ∫ y : ℝ, ‖mellin (f : ℝ → ℂ) (((s : ℝ) : ℂ) + y * I)‖ := by
  obtain ⟨he, h0, _⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have hconv : MellinConvergent (f : ℝ → ℂ) ((s : ℝ) : ℂ) := by
    refine mellinConvergent_cap he h0 ?_
    rw [Complex.ofReal_re]
    have : (-1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hvert := verticalIntegrable_mellin_cap s hs f hf
  have hinv := mellinInv_mellin_eq (s : ℝ) (f : ℝ → ℂ) hx hconv hvert f.continuous.continuousAt
  rw [← hinv]
  exact norm_mellinInv_le (s : ℝ) (mellin (f : ℝ → ℂ)) hx

end RHTower

end
