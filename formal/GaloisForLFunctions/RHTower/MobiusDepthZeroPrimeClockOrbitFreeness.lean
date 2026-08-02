import GaloisForLFunctions.HTGeometry.PrimeClockCyclicOrbitFreeness
import GaloisForLFunctions.RHTower.MobiusDepthZeroPrimeClockPhaseNodeNoGo

/-!
# Route E depth-zero source has a free complete prime-clock orbit

The canonical Route E depth-zero divided-log source is active on every prime ray.  Polynomial
clock saturation therefore promotes its nonzero class to a free cyclic module: every finite
linear combination of its logarithmic clock jets is nonzero modulo finite-prime Euler data.

Both unrotated and rotated clocks are recorded.  The rotated version is the formal normalization
used by logarithmic differentiation and the exact analytic prime-clock correspondence.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open Polynomial

noncomputable section

/-- Complete unrotated logarithmic-clock orbit of the Route E depth-zero all-prime source. -/
def routeEDepthZeroPrimeClockOrbit (k : ℕ) : PrimeProfileClockQuotient :=
  rayClockPolynomialOrbit primePowerClockRay primePowerClockWeight
    routeEDepthZeroPrimeClockProfile k

/-- Complete rotated logarithmic-clock orbit, in the normalization used by formal
differentiation. -/
def routeEDepthZeroRotatedPrimeClockOrbit (k : ℕ) : PrimeProfileClockQuotient :=
  rayClockPolynomialOrbit primePowerClockRay rotatedPrimePowerClockWeight
    routeEDepthZeroPrimeClockProfile k

/-- The unrotated Route E prime-clock orbit is free modulo every finite-prime Euler profile. -/
theorem routeEDepthZeroPrimeClockOrbit_linearIndependent :
    LinearIndependent ℂ routeEDepthZeroPrimeClockOrbit := by
  exact rayClockPolynomialOrbit_linearIndependent_of_not_local
    primePowerClockRay primePowerClockWeight primePowerClockWeight_injective
    routeEDepthZeroPrimeClockProfile routeEDepthZeroPrimeClockProfile_not_local

/-- The rotated differential-clock orbit is equally free. -/
theorem routeEDepthZeroRotatedPrimeClockOrbit_linearIndependent :
    LinearIndependent ℂ routeEDepthZeroRotatedPrimeClockOrbit := by
  exact rayClockPolynomialOrbit_linearIndependent_of_not_local
    primePowerClockRay rotatedPrimePowerClockWeight
    rotatedPrimePowerClockWeight_injective routeEDepthZeroPrimeClockProfile
    routeEDepthZeroPrimeClockProfile_not_local

/-- Every nonzero polynomial in the Route E logarithmic clock remains globally nonlocal. -/
theorem routeEDepthZeroPrimeClockPolynomial_not_local
    (P : ℂ[X]) (hP : P ≠ 0) :
    ¬ PrimePowerClockLocal
      (primePowerClockPolynomialApply P routeEDepthZeroPrimeClockProfile) := by
  exact (not_primePowerClockLocal_polynomialClockApply_iff
    P hP routeEDepthZeroPrimeClockProfile).mpr
    routeEDepthZeroPrimeClockProfile_not_local

/-- Rotated differential version of polynomial nonlocality. -/
theorem routeEDepthZeroRotatedPrimeClockPolynomial_not_local
    (P : ℂ[X]) (hP : P ≠ 0) :
    ¬ PrimePowerClockLocal
      (rotatedPrimePowerClockPolynomialApply P
        routeEDepthZeroPrimeClockProfile) := by
  rw [rotatedPrimePowerClockPolynomialApply_local_iff
    P hP routeEDepthZeroPrimeClockProfile]
  exact routeEDepthZeroPrimeClockProfile_not_local

end

end RHTower
