import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary

/-!
# Integral-orbit collapse of the standard low-frequency Kerr response

The hidden-conformal low-frequency spin-`s` Kerr retarded response contains two
frequency-dependent Gamma ratios. In natural complexified left/right frequency coordinates,
their shift separations are `1 - 2*h + 2*s` and `1 - 2*h`.

The spin-weighted spherical-harmonic eigenvalue fixes `h = ell + 1`. For integral angular
momentum `ell` and spin `s`, both separations are integers. The general Veneziano Gamma-ratio
boundary therefore puts both channels in the differentially algebraic sector.

This module formalizes the exact differential-algebraic specialization. The physical
identification of the Kerr response is external to Lean; no claim is made about finite-frequency
spheroidal deformation or the exact confluent-Heun connection problem.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Natural-coordinate left-moving Gamma ratio of the standard low-frequency spin-`s` Kerr
response, with conformal weight `h = ell + 1`. -/
def kerrLowFrequencyLeftGammaRatioMero (ell : ℕ) (s : ℤ) :
    meroField Set.univ :=
  reducedVenezianoAmplitudeMero
    ((ell : ℂ) + 1 - (s : ℂ))
    (1 - 2 * ((ell : ℂ) + 1) + 2 * (s : ℂ))

/-- Natural-coordinate right-moving Gamma ratio of the standard low-frequency Kerr response,
with conformal weight `h = ell + 1`. -/
def kerrLowFrequencyRightGammaRatioMero (ell : ℕ) :
    meroField Set.univ :=
  reducedVenezianoAmplitudeMero
    ((ell : ℂ) + 1)
    (1 - 2 * ((ell : ℂ) + 1))

/-- **Left-channel integral-orbit collapse.** Angular-momentum and spin quantization make the
left Gamma separation an integer, hence the frequency kernel is differentially algebraic. -/
theorem differentialAlgebraicOver_kerrLowFrequencyLeftGammaRatioMero
    (ell : ℕ) (s : ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrLowFrequencyLeftGammaRatioMero ell s) := by
  apply differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_of_integerShift
  refine ⟨2 * s - 2 * (ell : ℤ) - 1, ?_⟩
  push_cast
  ring

/-- **Right-channel integral-orbit collapse.** Angular-momentum quantization makes the right
Gamma separation an odd negative integer, hence the frequency kernel is differentially
algebraic. -/
theorem differentialAlgebraicOver_kerrLowFrequencyRightGammaRatioMero
    (ell : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrLowFrequencyRightGammaRatioMero ell) := by
  apply differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_of_integerShift
  refine ⟨-2 * (ell : ℤ) - 1, ?_⟩
  push_cast
  ring

end

end GaloisForLFunctions
