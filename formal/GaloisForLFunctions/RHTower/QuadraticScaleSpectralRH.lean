import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.ModulusSlopeBudget
import GaloisForLFunctions.RHTower.WeightOneInversion

/-!
# Quadratic scale-spectrum criterion for the Riemann hypothesis

The weight-one scale inversion exchanges the Mellin power profiles `t⁻ʷ` and
`t⁻⁽¹⁻ʷ⁾`, while the commuting quadratic scale Hamiltonian `D² + D` assigns
both profiles the reflection-invariant spectral parameter `w(w - 1)`.

This file closes the right end of that detour.  Reality of `ρ(ρ - 1)` at every
zero `ρ` of the completed xi function is equivalent to the Riemann hypothesis.
The converse uses two unconditional source facts already in the tree: every xi
zero lies in the open critical strip, and xi has no real zero there.

No spectral realization is asserted here.  The missing left-hand theorem is to
construct, from the theta--Euler--Gamma source without reading the xi divisor,
a self-adjoint realization of the quadratic scale Hamiltonian for which a xi
zero forces `ρ(ρ - 1)` into the spectrum.
-/

open Complex Set

namespace RHTower

/-- The positive-sign convention for the scale-Hamiltonian spectral parameter.  On
`L²(ℝ₊, dt)`, the formal adjoint relation `D† = -D-1` makes `-D(D+1) = D†D`, so a
power mode `t⁻ʷ` carries energy `-w(w-1)`. -/
def quadraticScaleEnergy (w : ℂ) : ℂ := -(w * (w - 1))

/-- Centering the reflection coordinate turns the scale energy into a square plus `1/4`. -/
theorem quadraticScaleEnergy_eq_centered (w : ℂ) :
    quadraticScaleEnergy w = 1 / 4 - (w - 1 / 2) ^ 2 := by
  unfold quadraticScaleEnergy
  ring

/-- Reality of the reflection-invariant quadratic scale parameter at every xi zero. -/
def XiQuadraticSpectralReality : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → (quadraticScaleEnergy ρ).im = 0

/-- RH puts every xi zero on the reflection line, where `ρ(ρ-1)` is real. -/
theorem xiQuadraticSpectralReality_of_rh (hRH : RiemannHypothesis) :
    XiQuadraticSpectralReality := by
  intro ρ hρ
  have hre := xi_zero_re_eq_half_of_RH hRH hρ
  rw [quadraticScaleEnergy, neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, hre]
  ring

/-- If the quadratic scale parameter is real at every xi zero, then RH holds. -/
theorem riemannHypothesis_of_xiQuadraticSpectralReality
    (hspec : XiQuadraticSpectralReality) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hright hρ
  have hstrip := xi_zero_re_mem_open_unit hρ
  have hquad := hspec ρ hρ
  have him : ρ.im = 0 := by
    rw [quadraticScaleEnergy, neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im] at hquad
    have hre : 1 / 2 < ρ.re := mem_rightHalf.mp hright
    nlinarith
  have hrho : ρ = (ρ.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using him
  have hne := xi_ne_zero_real_anchor hstrip.1 hstrip.2
  rw [hrho] at hρ
  exact hne hρ

/-- Exact terminal closure of the quadratic scale-spectrum detour. -/
theorem xiQuadraticSpectralReality_iff_riemannHypothesis :
    XiQuadraticSpectralReality ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_xiQuadraticSpectralReality,
    xiQuadraticSpectralReality_of_rh⟩

end RHTower
