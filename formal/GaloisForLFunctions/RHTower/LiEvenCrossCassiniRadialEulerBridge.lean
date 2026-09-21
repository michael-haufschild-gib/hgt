import GaloisForLFunctions.RHTower.LiEvenCrossTwoScaleRadialGeneratingLaw
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniSourceJet

/-!
# LI radial response as a Cassini Euler defect

The full LI completed-Abel adjacent-current tower is a divided difference of the
first radial response.  This module identifies that response with one differential
expression in the logarithmic derivative of the fixed Cassini source.  Thus any
complex continuation or singular-support law for LI must act on this one source
object before coefficient extraction; the result does not assert such a law.
-/

open Complex

namespace RHTower

noncomputable section

/-- The prime--Gamma form of the LI radial response.  This is defined before taking
the Cassini bridge, so its source window remains visible. -/
def liEvenCrossPrimeArchRadialDilationResponse (y : ℝ) : ℝ :=
  y * ((primeArchShiftedReciprocalMoment y 0).re -
    y * (primeArchShiftedReciprocalMoment y 1).re)

/-- On the complete prime--Gamma convergence window, the prime--Gamma radial response is
exactly the LI divisor radial response. -/
theorem liEvenCrossPrimeArchRadialDilationResponse_eq
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2) :
    liEvenCrossPrimeArchRadialDilationResponse y =
      liEvenCrossRadialDilationResponse y := by
  simp only [liEvenCrossPrimeArchRadialDilationResponse,
    liEvenCrossRadialDilationResponse]
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax]

/-- The complex LI radial response is the Euler differential defect of the logarithmic
derivative of the one fixed Cassini source, evaluated at its moving center. -/
theorem liEvenCrossComplexRadialDilationResponse_eq_cassiniEulerDefect
    {y : ℝ} (hy : 0 < y) :
    liEvenCrossComplexRadialDilationResponse y =
      2 * (y : ℂ) *
        ((y : ℂ) * iteratedDeriv 1 (logDeriv xiSquaredSeamCassiniSource)
          (1 - (y : ℂ)) -
          logDeriv xiSquaredSeamCassiniSource (1 - (y : ℂ))) := by
  have h0 := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 0
  have h1 := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 1
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at h0
  norm_num [iteratedDeriv_one] at h1
  rw [liEvenCrossComplexRadialDilationResponse, ← h0, ← h1]
  simp only [iteratedDeriv_one]
  ring

/-- Real LI radial response is the real trace of the same Cassini Euler defect. -/
theorem liEvenCrossRadialDilationResponse_eq_cassiniEulerDefect_re
    {y : ℝ} (hy : 0 < y) :
    liEvenCrossRadialDilationResponse y =
      (2 * (y : ℂ) *
        ((y : ℂ) * iteratedDeriv 1 (logDeriv xiSquaredSeamCassiniSource)
          (1 - (y : ℂ)) -
          logDeriv xiSquaredSeamCassiniSource (1 - (y : ℂ)))).re := by
  have h := congrArg Complex.re
    (liEvenCrossComplexRadialDilationResponse_eq_cassiniEulerDefect hy)
  rw [liEvenCrossComplexRadialDilationResponse_eq_ofReal hy.le] at h
  simpa using h

end

end RHTower
