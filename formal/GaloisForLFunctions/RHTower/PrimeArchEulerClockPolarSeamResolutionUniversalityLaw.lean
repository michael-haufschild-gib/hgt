import GaloisForLFunctions.RHTower.CCMEulerEssentialBoundaryLayerCorrespondence
import GaloisForLFunctions.RHTower.PrimeArchPolarSeamRemoval

/-!
# Prime--arch Euler clock/polar-seam resolution universality

The same positive Euler prime flux has two exact critical-boundary resolutions.  Multiplicative
normalization along every critical ray selects the unit exponential characteristic function.
Additive subtraction of the archimedean logarithmic derivative removes the polar seam, and the
completed Xi flux is the unique analytic completion of that punctured germ.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Complete multiplicative/additive critical-boundary resolution certificate for the positive
Euler prime flux. -/
structure PrimeArchEulerClockPolarSeamResolutionCertificate (t : ℝ) : Prop where
  criticalClock :
    Tendsto (fun sigma : ℝ => ccmEulerPrimeCurrentClockResponse sigma t)
      (nhdsWithin 1 (Ioi 1))
      (nhds (charFun (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) t))
  seamAnalytic :
    AnalyticAt ℂ seamFluxCochain 1
  seamGerm :
    (fun s : ℂ => infinitePrimeFlux s - logDeriv archFactor s) =ᶠ[𝓝[≠] (1 : ℂ)]
      seamFluxCochain
  seamUnique :
    ∀ g : ℂ → ℂ, AnalyticAt ℂ g 1 →
      (fun s : ℂ => infinitePrimeFlux s - logDeriv archFactor s) =ᶠ[𝓝[≠] (1 : ℂ)] g →
        g =ᶠ[𝓝 (1 : ℂ)] seamFluxCochain

/-- **Prime--arch Euler clock/polar-seam resolution universality law.**  At every real clock
frequency, multiplicative normalization of the actual positive von Mangoldt current has the unit
exponential limit.  Independently of frequency, subtracting the archimedean logarithmic
derivative gives the completed Xi seam flux, which is analytic at `1` and is the unique analytic
completion of the source-built punctured germ. -/
theorem primeArchEuler_clockPolarSeamResolutionUniversality (t : ℝ) :
    PrimeArchEulerClockPolarSeamResolutionCertificate t where
  criticalClock :=
    tendsto_ccmEulerPrimeCurrentClockResponse_eq_exponentialCharFun t
  seamAnalytic :=
    analyticAt_seamFluxCochain_one
  seamGerm :=
    primeArchPolarFlux_eventuallyEq_seamFluxCochain_one
  seamUnique :=
    fun _ hg hsource =>
      primeArchPolarFlux_analyticCompletion_unique_one hg hsource

end

end RHTower
