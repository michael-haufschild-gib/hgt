import GaloisForLFunctions.RHTower.BandQuadraticFormFourier
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The band quadratic form is the frequency-window energy

The band quadratic form of a test function supported in `[-1, 1]` is exactly the energy of its Fourier
transform inside the window `|xi| <= c/(2 pi)`:

```text
∫∫ sinc_c(x-y) psi(x) psi(y) dx dy = ∫_(-c/2pi)^(c/2pi) ‖𝓕 psi (xi)‖² d xi.
```

This is the concentration reading of the band operator: its quadratic form measures how much of the
function's spectrum lies inside the band, so its largest eigenvalue is the best possible spectral
concentration of a function supported in `[-1, 1]`, and the leakage `1 - lambda` is the least possible
spectral tail.

Two conversions are involved.  The first identifies the card's band moment
`F_a psi = ∫_(-1)^1 psi(x) e^{i a x} dx` with mathlib's Fourier integral of the truncation of `psi`, at
frequency `-a/(2 pi)` — the `2 pi` sits in mathlib's character.  The second is the change of variables
`xi = -c t/(2 pi)` that turns the average over the band parameter `t` into an integral over the
frequency window; the Jacobian cancels the factor `c/(2 pi)` of the energy identity exactly.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-- The truncation of a real function to the band, as a complex-valued function on the line. -/
def bandTrunc (ψ : ℝ → ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Icc (-1 : ℝ) 1) (fun x => (ψ x : ℂ))

/-- **The band moment is a Fourier integral.**  The card's finite-Fourier moment at frequency `a` is
mathlib's Fourier integral of the truncation at frequency `-a/(2 pi)`. -/
theorem bandFourier_eq_fourier (a : ℝ) (ψ : ℝ → ℝ) :
    bandFourier a ψ = 𝓕 (bandTrunc ψ) (-(a / (2 * Real.pi))) := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Real.fourier_eq']
  have hind : (∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (inner ℝ v (-(a / (2 * Real.pi))))) : ℂ)
        * Complex.I) • bandTrunc ψ v)
      = ∫ v in Set.Icc (-1 : ℝ) 1, Complex.exp ((↑(-2 * Real.pi *
        (inner ℝ v (-(a / (2 * Real.pi))))) : ℂ) * Complex.I) • ((ψ v : ℂ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [bandTrunc, Set.indicator_apply]
    split_ifs with hv
    · rfl
    · rw [smul_zero]
  rw [hind, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, bandFourier]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hinner : (inner ℝ x (-(a / (2 * Real.pi))) : ℝ) = -(x * (a / (2 * Real.pi))) := by
    simp
    ring
  rw [hinner]
  have hexpR : (-2 * Real.pi * -(x * (a / (2 * Real.pi))) : ℝ) = a * x := by
    field_simp
  have hexp : ((-2 * Real.pi * -(x * (a / (2 * Real.pi))) : ℝ) : ℂ) = ((a * x : ℝ) : ℂ) := by
    rw [hexpR]
  rw [hexp, smul_eq_mul]
  rw [mul_comm ((ψ x : ℂ)) _]
  congr 1
  push_cast
  ring

/-- **The band average of moments is the frequency-window energy.**  The change of variables
`xi = -c t/(2 pi)` turns the band average into an integral over the window, and its Jacobian cancels
the prefactor. -/
theorem energy_eq_frequency_window {c : ℝ} (hc : 0 < c) (ψ : ℝ → ℝ) :
    (c / (2 * Real.pi)) * ∫ t in (-1 : ℝ)..1, ‖bandFourier (c * t) ψ‖ ^ 2
      = ∫ ξ in -(c / (2 * Real.pi))..(c / (2 * Real.pi)), ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℝ := c / (2 * Real.pi) with hk
  have hkpos : 0 < k := by
    rw [hk]
    positivity
  have hkne : k ≠ 0 := ne_of_gt hkpos
  set g : ℝ → ℝ := fun ξ => ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2 with hg
  have hstep1 : (∫ t in (-1 : ℝ)..1, ‖bandFourier (c * t) ψ‖ ^ 2)
      = ∫ t in (-1 : ℝ)..1, g (-(k * t)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [bandFourier_eq_fourier (c * t) ψ]
    have hfreq : c * t / (2 * Real.pi) = k * t := by
      rw [hk]
      ring
    rw [hfreq]
  have hstep2 : (∫ t in (-1 : ℝ)..1, g (-(k * t))) = ∫ t in (-1 : ℝ)..1, g (k * t) := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun t => g (k * t))
    simpa using h
  have hstep3 : (∫ t in (-1 : ℝ)..1, g (k * t)) = k⁻¹ * ∫ ξ in (k * (-1))..(k * 1), g ξ := by
    have h := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1) g hkne
    rw [h, smul_eq_mul]
  rw [hstep1, hstep2, hstep3]
  have hends : k * (-1) = -k ∧ k * 1 = k := by
    constructor <;> ring
  rw [hends.1, hends.2, ← mul_assoc, mul_inv_cancel₀ hkne, one_mul]

/-- **The band quadratic form is the frequency-window energy.** -/
theorem double_integral_sincKernel_eq_frequency_energy {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (ψ x * ψ y))
      = ∫ ξ in -(c / (2 * Real.pi))..(c / (2 * Real.pi)), ‖𝓕 (bandTrunc ψ) ξ‖ ^ 2 := by
  rw [double_integral_sincKernel_eq_energy c hψ, energy_eq_frequency_window hc ψ]

end GaloisForLFunctions.RHTower

end
