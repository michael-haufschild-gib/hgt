import GaloisForLFunctions.RHTower.AtomicBernsteinPacketRpowGrowth
import GaloisForLFunctions.RHTower.PrimeArchBernsteinRpowGrowth

/-!
# Exact atomic realization of the endpoint Xi Bernstein packet

Every coefficient of the prime--archimedean endpoint packet is exactly the absolutely summable
reciprocal-square divisor packet at the normalized Xi coordinate.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- The endpoint prime--archimedean packet is exactly the reciprocal-square atomic packet. -/
theorem primeArchEndpointBernsteinPacket_eq_atomic :
    primeArchEndpointBernsteinPacket =
      atomicBernsteinPacket xiZeroCopyReciprocalSquare
        xiEndpointNormalizedReciprocalSquare := by
  funext n i
  rw [primeArchEndpointBernsteinPacket, atomicBernsteinPacket,
    atomicBernsteinCoefficient]
  have hsource := xiCentralRadiusNormalizedPolynomialMoment_eq_source
    primeArchEndpointHausdorffRadius (bernsteinPolynomial ℝ n i)
  have htsum := xiCentralRadiusNormalizedPolynomialMoment_eq_tsum
    primeArchEndpointHausdorffRadius (bernsteinPolynomial ℝ n i)
  rw [hsource] at htsum
  rw [bernsteinCoefficient, htsum]
  apply tsum_congr
  intro q
  rw [atomicBernsteinCoefficientTerm, xiEndpointNormalizedReciprocalSquare,
    bernsteinPolynomial]
  simp only [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_mul,
    Polynomial.eval₂_natCast, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_one]
  ring

end

end RHTower
