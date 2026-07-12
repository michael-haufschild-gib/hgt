import GaloisForLFunctions.RHTower.CCMComplexMellinColligation
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# The continued Xi source factors through the critical Mellin defect

The polar--prime critical Mellin defect is initially defined by convergent Laplace channels on
the right half-plane.  Its source formula has a canonical meromorphic continuation.  After the
centered coordinate change, that continuation and the fixed archimedean logarithmic derivative
recover the full continued prime--Gamma trace identically.

Consequently the RH-bearing continued Cauchy kernel is the conjugate divided difference of one
explicit polar--critical-Mellin--archimedean source.  This is a value-relation bridge only: it does
not assert a sign for the continued defect kernel.
-/

open scoped ComplexConjugate
open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Centered Xi source coordinate shifted to the critical Mellin variable. -/
def xiCriticalMellinCoordinate (z : ℂ) : ℂ :=
  -1 / 2 + z * I

/-- Canonical meromorphic source expression continuing the polar--prime critical Mellin defect. -/
def continuedCriticalMellinDefect (u : ℂ) : ℂ :=
  1 / u + 1 / (u + 1) + logDeriv riemannZeta (u + 1)

/-- The continued defect agrees with the convergent polar--prime Laplace channel on its
right-half-plane domain. -/
theorem criticalMellinDefectLaplaceChannelComplex_eq_continued
    {u : ℂ} (hu : 0 < u.re) :
    criticalMellinDefectLaplaceChannelComplex u =
      continuedCriticalMellinDefect u := by
  rw [criticalMellinDefectLaplaceChannelComplex,
    continuousPolarLaplaceChannelComplex_eq hu,
    vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv hu]
  rw [continuedCriticalMellinDefect, logDeriv_apply]
  ring

/-- The polar--continued-defect--archimedean representation of the centered source trace. -/
def continuedPolarMellinArchSourceTrace (z : ℂ) : ℂ :=
  let u := xiCriticalMellinCoordinate z;
  -I *
    ((1 / u + 1 / (u + 1)) - continuedCriticalMellinDefect u -
      logDeriv archFactor (1 / 2 + z * I))

/-- Globally, the continued prime--Gamma trace is exactly the explicit polar background minus the
continued critical Mellin defect and the archimedean logarithmic derivative. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_continuedPolarMellinArch (z : ℂ) :
    continuedPrimeArchSourceRelativeTrace z =
      continuedPolarMellinArchSourceTrace z := by
  rw [continuedPrimeArchSourceRelativeTrace, continuedPolarMellinArchSourceTrace,
    continuedCriticalMellinDefect, xiCriticalMellinCoordinate, infinitePrimeFlux]
  have hcoord : -1 / 2 + z * I + 1 = 1 / 2 + z * I := by ring
  rw [hcoord]
  ring

/-- The RH-bearing continued Cauchy kernel is the conjugate divided difference of the explicit
continued polar--critical-Mellin--archimedean source. -/
theorem ccmContinuedCauchyKernel_eq_continuedPolarMellinArch_dividedDifference
    (z w : ℂ) :
    ccmContinuedCauchyKernel z w =
      (continuedPolarMellinArchSourceTrace ((starRingEnd ℂ) w) -
        continuedPolarMellinArchSourceTrace z) /
          (z - (starRingEnd ℂ) w) := by
  rw [ccmContinuedCauchyKernel,
    continuedPrimeArchSourceRelativeTrace_eq_continuedPolarMellinArch,
    continuedPrimeArchSourceRelativeTrace_eq_continuedPolarMellinArch]

/-- After the archimedean logarithmic derivative is expanded, its two rational boundary terms
cancel the displayed polar background exactly.  Thus the apparently three-part source is simply
the critical Mellin defect plus the Gamma connection. -/
def continuedMellinGammaSourceTrace (z : ℂ) : ℂ :=
  I * (continuedCriticalMellinDefect (xiCriticalMellinCoordinate z) +
    gammaRealLogConnection (1 / 2 + z * I))

/-- The polar--Gamma decomposition does not create an independent domination problem: off the
two archimedean boundary points it reduces identically to the Mellin-defect--Gamma source. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
    {z : ℂ} (hs : 0 < (1 / 2 + z * I).re)
    (h0 : 1 / 2 + z * I ≠ 0) (h1 : 1 / 2 + z * I ≠ 1) :
    continuedPrimeArchSourceRelativeTrace z =
      continuedMellinGammaSourceTrace z := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_continuedPolarMellinArch,
    continuedPolarMellinArchSourceTrace, continuedMellinGammaSourceTrace,
    logDeriv_archFactor_closed hs h0 h1]
  rw [xiCriticalMellinCoordinate]
  have hsub : 1 / 2 + z * I - 1 = -1 / 2 + z * I := by ring
  rw [hsub]
  ring

/-- On the regular continued-Cauchy source domain, the RH-bearing kernel is the divided difference
of the reduced Mellin-defect--Gamma source. -/
theorem ccmContinuedCauchyKernel_eq_continuedMellinGamma_dividedDifference
    {z w : ℂ} (hz : CCMContinuedCauchyDomain z)
    (hw : CCMContinuedCauchyDomain w) :
    ccmContinuedCauchyKernel z w =
      (continuedMellinGammaSourceTrace ((starRingEnd ℂ) w) -
        continuedMellinGammaSourceTrace z) /
          (z - (starRingEnd ℂ) w) := by
  rw [ccmContinuedCauchyKernel,
    continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
      hz.1 (by
        intro h
        have hpos := hz.1
        rw [h] at hpos
        norm_num at hpos) hz.2.1,
    continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
      hw.2.2.2.1 (by
        intro h
        have hpos := hw.2.2.2.1
        rw [h] at hpos
        norm_num at hpos) hw.2.2.2.2.1]

end

end RHTower
