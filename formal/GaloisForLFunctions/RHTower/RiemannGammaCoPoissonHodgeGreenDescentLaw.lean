import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison
import GaloisForLFunctions.RHTower.EulerPrimitivePolarizedHodgeBetaTransgression
import GaloisForLFunctions.RHTower.RiemannSingularGreenHodgeAdmissionLaw

/-!
# Gamma/co-Poisson Hellinger--Hodge Green descent law

The Euler head/tail occupation split supplies a Bernoulli information
geometry.  Its forced odd Hodge scale is reciprocal Fisher whitening, its
cross-channel density is the Hellinger geometric mean, and the common
Laplace test transforms that density into an exact Beta/Gamma quotient.

The same odd Hodge polarization lifts through the exact
Calderón--Witt Green incidence to the actual moving-horizon
Gamma/co-Poisson boundary comparison.  This file proves that its
reflection defect descends through all exact secondary Green boundaries
exactly at zero modular displacement.

At a Xi-divisor point, that displacement is

`2 * (re rho - 1 / 2)`.

Consequently, descent of the actual constructed boundary comparison at a
point is exactly the critical-line condition, and descent on every divisor
fibre is equivalent to RH.  No existence conjecture for the transport
remains in this reduction; only its global divisor-indexed descent is open.
-/

namespace RHTower

open Complex

noncomputable section

/--
The actual Gamma/co-Poisson Hodge-boundary reflection defect annihilates
the whole exact Calderón--Witt incidence space exactly at zero modular
displacement.  A single canonical cross-prime Green boundary detects the
obstruction.
-/
theorem
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq_zero_iff
    (a : ℝ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a = 0 ↔
      a = 0 := by
  rw [deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq,
    deningerCalderonWittGammaReflectionOddScalarTransport_eq_zero_iff]

/--
Pointwise Gamma/co-Poisson Green descent at a Riemann boundary point is
exactly the critical-line condition.
-/
theorem
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_boundaryFracture_eq_zero_iff
    (rho : ℂ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
        (xiNearbyPoleDualityAdjunctionFracture rho).re = 0 ↔
      rho.re = 1 / 2 := by
  rw [
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq_zero_iff,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

/--
The actual polarized Gamma/co-Poisson boundary comparison descends through
all exact secondary Green boundaries over the Xi divisor.
-/
def XiGammaCoPoissonHodgeGreenBoundaryDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
        (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)).re = 0

/--
**Hellinger--Hodge Green descent classification.**

Global descent of the actual source-derived Gamma/co-Poisson polarized
boundary comparison through exact secondary Green boundaries is equivalent
to boundary-character neutrality, hence to RH.
-/
theorem xiGammaCoPoissonHodgeGreenBoundaryDescends_iff_riemannHypothesis
    :
    XiGammaCoPoissonHodgeGreenBoundaryDescends ↔
      RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  constructor
  · intro h rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    exact
      (deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_boundaryFracture_eq_zero_iff
        (rho : ℂ)).1 (h rho)
  · intro h rho
    apply
      (deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_boundaryFracture_eq_zero_iff
        (rho : ℂ)).2
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 (h rho)

end

end RHTower
