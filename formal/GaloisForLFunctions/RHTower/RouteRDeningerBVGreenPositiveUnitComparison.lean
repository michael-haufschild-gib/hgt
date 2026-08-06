import GaloisForLFunctions.RHTower.DeningerOrdinaryIntegerBVGreenStokesRadialComparison
import GaloisForLFunctions.RHTower.CCMRationalAdelicCompletedXiFixedCoronaPolarization
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldBarrelledSourceSelector
import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapSingularStokesLaw

/-!
# Route-R / Deninger BV--Green positive-unit comparison

The literal reflected ordinary-integer BV--Green boundary at degree six and
Route R's fixed-fibre Hodge-mate coefficient are not merely zero-set
equivalent.  They differ by a canonical strictly positive unit.  The unit is
written with hyperbolic sinc, so no coefficient is divided out and the
identity remains meaningful on the critical fibre.

This identifies the explicit pre-divisor source boundary whose physical
cyclic descent would annihilate Route R's coefficient.  It does not assert
that descent: physical evaluation is not declared cyclic.
-/

open Complex

namespace RHTower

noncomputable section

/-- Division-free hyperbolic-sinc normalization at the critical fibre. -/
def routeRDeningerHyperbolicSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

/-- Hyperbolic sinc has positive orientation on both radial branches. -/
theorem routeRDeningerHyperbolicSinc_pos (x : ℝ) :
    0 < routeRDeningerHyperbolicSinc x := by
  by_cases hx : x = 0
  · simp [routeRDeningerHyperbolicSinc, hx]
  · rw [routeRDeningerHyperbolicSinc, if_neg hx]
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hxneg) hxneg
    · exact div_pos (Real.sinh_pos_iff.mpr hxpos) hxpos

/-- Exact multiplication law, including the critical fibre. -/
theorem mul_routeRDeningerHyperbolicSinc (x : ℝ) :
    x * routeRDeningerHyperbolicSinc x = Real.sinh x := by
  by_cases hx : x = 0
  · simp [routeRDeningerHyperbolicSinc, hx]
  · rw [routeRDeningerHyperbolicSinc, if_neg hx]
    field_simp

/-- Canonical positive unit from one Route-R prime attenuation to the fixed
degree-six Deninger mate curvature. -/
def routeRDeningerBVGreenPositiveUnit
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℝ :=
  (2 * Real.log 6 *
      routeRDeningerHyperbolicSinc
        (primeDepthBVWoldXiCenteredRate rho * Real.log 6)) /
    primeDepthBVWoldReesCoronaAdjacentAttenuation p

/-- The comparison unit remains strictly positive in both Gamma
orientations and on the critical fibre. -/
theorem routeRDeningerBVGreenPositiveUnit_pos
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    0 < routeRDeningerBVGreenPositiveUnit p rho := by
  rw [routeRDeningerBVGreenPositiveUnit]
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (routeRDeningerHyperbolicSinc_pos _))
    (primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p)

/-- **Positive-unit curvature comparison.**  Deninger's fixed degree-six
tensor-square mate curvature is the positive unit times Route R's actual
retained Hodge-mate coefficient. -/
theorem deningerTensorSquareRadialMateCurvature_six_eq_routeR_positiveUnit_mul
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerTensorSquareRadialMateCurvature 6 (rho : ℂ) =
      routeRDeningerBVGreenPositiveUnit p rho *
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho := by
  rw [deningerTensorSquareRadialMateCurvature_eq_sinh 6 (rho : ℂ) (by norm_num),
    ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    primeDepthBVWoldReesCoronaWeight_adjacent_eq,
    routeRDeningerBVGreenPositiveUnit]
  change
    2 * Real.sinh
        (primeDepthBVWoldXiCenteredRate rho * Real.log 6) = _
  have hk : primeDepthBVWoldReesCoronaAdjacentAttenuation p ≠ 0 :=
    (primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p).ne'
  rw [← mul_routeRDeningerHyperbolicSinc
    (primeDepthBVWoldXiCenteredRate rho * Real.log 6)]
  field_simp [hk]

/-- Literal reflected physical evaluation of the pre-divisor
ordinary-integer BV--Green Hochschild boundary at degree six. -/
def routeRDeningerBVGreenReflectedBoundary
    (rho : XiDivisorSupport) : ℝ :=
  6 *
    (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ) -
      deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6
        (1 - star (rho : ℂ)))

/-- The literal BV--Green source boundary has the same positive-unit
comparison with Route R. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_positiveUnit_mul
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho =
      routeRDeningerBVGreenPositiveUnit p rho *
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho := by
  rw [routeRDeningerBVGreenReflectedBoundary]
  calc
    6 *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6
            (1 - star (rho : ℂ))) =
        deningerTensorSquareRadialMateCurvature 6 (rho : ℂ) := by
          simpa using
            deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
              (n := 6) (by norm_num) (rho : ℂ)
    _ = _ :=
      deningerTensorSquareRadialMateCurvature_six_eq_routeR_positiveUnit_mul p rho

/-- Source-boundary nullity and explicit Route-R coefficient nullity are
exactly equivalent, with no Xi-jet division. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  rw [routeRDeningerBVGreenReflectedBoundary_eq_positiveUnit_mul p rho,
    mul_eq_zero]
  exact or_iff_right (routeRDeningerBVGreenPositiveUnit_pos p rho).ne'

/-- The fixed same-fibre norm identity is precisely nullity of the literal
reflected BV--Green source boundary. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sameFiberNormIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho :=
  (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
      p rho).symm

/-- The fixed source-dagger identity is precisely nullity of the literal
reflected BV--Green source boundary. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sourceDaggerIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho :=
  (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero
    p rho).trans
    (ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero
      p rho).symm

/-- The actual ordered Gamma boundary coefficient uses the same positive
unit, followed only by its already-proved positive Gamma calibration. -/
theorem deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_routeR_positiveUnit_mul
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) =
      (((deningerCalderonWittBaseGammaMateCalibration *
        routeRDeningerBVGreenPositiveUnit p rho) *
          ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℝ) : ℂ) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature]
  change
    ((deningerCalderonWittBaseGammaMateCalibration *
      deningerTensorSquareRadialMateCurvature 6 (rho : ℂ) : ℝ) : ℂ) = _
  rw [deningerTensorSquareRadialMateCurvature_six_eq_routeR_positiveUnit_mul p rho]
  push_cast
  ring

/-- The reflected BV--Green source boundary detects the critical line
without any prime choice. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact
    (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_hodgeMateCoefficient_eq_zero
      p2 rho).trans
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p2 rho)

/-- The existing cofinal source-normal producer obligation is exactly
nullity of the fixed degree-six BV--Green source boundary. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_cofinalEquicontinuity
    (sourceDepth : ℕ) (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      PrimeDepthBVWoldXiCofinalSourceNormalEquicontinuity sourceDepth rho :=
  (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half rho).trans
    (xiCofinalSourceNormalEquicontinuity_iff_re_eq_half sourceDepth rho).symm

/-- The previously isolated fixed-orientation singular Stokes law is the
same source-boundary nullity statement. -/
theorem routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_singularStokesFlat
    (rho : XiDivisorSupport) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half,
    ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Any honest completed barrelled-source certificate kills the literal
degree-six BV--Green boundary, not only an abstract centered scalar. -/
theorem PrimeDepthBVWoldBarrelledSourceCertificate.routeRDeningerBoundary_eq_zero
    {sourceDepth : ℕ} {rho : XiDivisorSupport}
    (cert : PrimeDepthBVWoldXiBarrelledSourceCertificate sourceDepth rho) :
    routeRDeningerBVGreenReflectedBoundary rho = 0 :=
  (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_re_eq_half rho).2
    (re_eq_half_of_barrelledSourceCertificate cert)

/-- A single fixed degree-six reflected source boundary is a complete global
Route-R endpoint.  This is a classifier, not an assertion of source cyclic
descent. -/
theorem forall_routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      routeRDeningerBVGreenReflectedBoundary rho = 0) ↔
      RiemannHypothesis := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  constructor
  · intro h
    exact
      (forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p2).1
        (fun rho =>
          (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sameFiberNormIdentity
            p2 rho).1 (h rho))
  · intro hRH rho
    exact
      (routeRDeningerBVGreenReflectedBoundary_eq_zero_iff_sameFiberNormIdentity
        p2 rho).2
        ((forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p2).2
          hRH rho)

end

end RHTower
