import GaloisForLFunctions.RHTower.XiMassHyperbolicFourierRepresentation
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCells
import GaloisForLFunctions.RHTower.XiMassRapidityPhaseGeometry

/-!
# The mass profile in the rapidity variable

The substitution `x = a sinh t` writes the mass Fourier profile as an integral over the rapidity
line whose amplitude is real and whose entire oscillation sits in one phase:

`F_u(h) = a ∫_ℝ cosh t · e^{-aσ cosh t} · e^{-i a (u cosh t + h sinh t)} dt`.

The phase `u cosh t + h sinh t` is exactly the mass phase whose hyperbolic collapse is proved in
`XiMassRapidityPhaseGeometry`: inside the light cone it is `q cosh(t+η)` with `q = √(u²−h²)` and
has the single stationary point `t = −η`; outside it is `r sinh(t+η)` and is never stationary.
Combining the two gives the geometric form of the kernel that the light-cone analysis uses.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The rapidity form of the mass Fourier integrand: a positive amplitude times the pure mass
phase `a(u cosh t + h sinh t)`. -/
def xiMassRapidityPhaseKernel (a sigma u h t : ℝ) : ℂ :=
  (Real.cosh t : ℂ) * ((Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ)
    * Complex.exp (-(I * ((a * (u * Real.cosh t + h * Real.sinh t) : ℝ) : ℂ)))

/-- The hyperbolic Fourier kernel is the amplitude `a` times the rapidity phase kernel. -/
theorem xiMassHyperbolicFourierKernel_eq_rapidity (a sigma u h t : ℝ) :
    xiMassHyperbolicFourierKernel a sigma u h t
      = (a : ℂ) * xiMassRapidityPhaseKernel a sigma u h t := by
  have h1 : Complex.exp (-((sigma : ℂ) + (u : ℂ) * I) * ((a * Real.cosh t : ℝ) : ℂ))
        * Complex.exp (-(I * (h : ℂ) * ((a * Real.sinh t : ℝ) : ℂ)))
      = ((Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ)
        * Complex.exp (-(I * ((a * (u * Real.cosh t + h * Real.sinh t) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [xiMassHyperbolicFourierKernel, xiMassRapidityPhaseKernel, mul_assoc, h1]
  push_cast
  ring

/-- The rapidity mass kernel is integrable whenever the damping and mass are positive.
This is scalar transport from the already-integrable hyperbolic kernel. -/
theorem integrable_xiMassRapidityPhaseKernel
    {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Integrable (xiMassRapidityPhaseKernel a sigma u h) := by
  have hhyper : Integrable (xiMassHyperbolicFourierKernel a sigma u h) :=
    integrable_xiMassHyperbolicFourierKernel ha hsigma
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha.ne'
  refine (hhyper.const_mul ((a : ℂ)⁻¹)).congr (ae_of_all _ fun t => ?_)
  change (a : ℂ)⁻¹ * xiMassHyperbolicFourierKernel a sigma u h t =
    xiMassRapidityPhaseKernel a sigma u h t
  rw [xiMassHyperbolicFourierKernel_eq_rapidity]
  field_simp

/-- **(8.1) The exact hyperbolic representation of the mass profile.**  The substitution
`x = a sinh t` turns the mass Fourier transform into a rapidity integral with real amplitude and
the single mass phase `a(u cosh t + h sinh t)`. -/
theorem stripFourier_xiMass_eq_integral_rapidityPhase {a sigma u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) :
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)
      = (a : ℂ) * ∫ t : ℝ, xiMassRapidityPhaseKernel a sigma u h t := by
  rw [stripFourier_xiMass_eq_integral_hyperbolicFourier ha hsigma, ← integral_const_mul]
  exact integral_congr_ae
    (ae_of_all _ fun t => xiMassHyperbolicFourierKernel_eq_rapidity a sigma u h t)

/-- The damped profile in rapidity form. -/
theorem xiMassCriticalDampedFourierProfile_eq_integral_rapidityPhase {a sigma u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalDampedFourierProfile a sigma u h
      = ((Real.exp (-h / 2) : ℝ) : ℂ) * (a : ℂ)
        * ∫ t : ℝ, xiMassRapidityPhaseKernel a sigma u h t := by
  rw [xiMassCriticalDampedFourierProfile, stripFourier_xiMass_eq_integral_rapidityPhase ha hsigma,
    mul_assoc]

/-! ## The two hyperbolic collapses of the kernel -/

/-- **(8.2) Inside the light cone the kernel oscillates in a single hyperbolic cosine.** -/
theorem xiMassRapidityPhaseKernel_timelike {a sigma u h : ℝ}
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h < u) (t : ℝ) :
    xiMassRapidityPhaseKernel a sigma u h t
      = (Real.cosh t : ℂ) * ((Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ)
        * Complex.exp (-(I * ((a * (Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ))
            * Real.cosh (t + timelikeRapidity u h)) : ℝ) : ℂ))) := by
  rw [xiMassRapidityPhaseKernel, massPhase_timelike hu hh hhu t]

/-- **(8.3) Outside the light cone the kernel oscillates in a single hyperbolic sine.** -/
theorem xiMassRapidityPhaseKernel_spacelike {a sigma u h : ℝ}
    (hu : 0 ≤ u) (hh : 0 < h) (huh : u < h) (t : ℝ) :
    xiMassRapidityPhaseKernel a sigma u h t
      = (Real.cosh t : ℂ) * ((Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ)
        * Complex.exp (-(I * ((a * (Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))
            * Real.sinh (t + spacelikeRapidity u h)) : ℝ) : ℂ))) := by
  rw [xiMassRapidityPhaseKernel, massPhase_spacelike hu hh huh t]

/-- **On the light cone the kernel oscillates in a pure exponential.** -/
theorem xiMassRapidityPhaseKernel_onCone (a sigma u t : ℝ) :
    xiMassRapidityPhaseKernel a sigma u u t
      = (Real.cosh t : ℂ) * ((Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ)
        * Complex.exp (-(I * ((a * (u * Real.exp t) : ℝ) : ℂ))) := by
  rw [xiMassRapidityPhaseKernel, massPhase_onCone u t]

end

end RHTower
