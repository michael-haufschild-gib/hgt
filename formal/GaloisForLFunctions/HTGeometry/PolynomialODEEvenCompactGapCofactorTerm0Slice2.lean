import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice0
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice1
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice2
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCorrectionSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapScalarNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Exact three-term coefficient convolution after the head has been independently checked. -/
def evenCompactGapCofactorTerm0Slice2Factored (u w : ℝ) : ℝ :=
  evenCompactGapHeadSlice0 u w *
      (evenCompactGapReflectedTwelveSlice2 u w + evenCompactGapCorrectionSlice2 u) +
    evenCompactGapHeadSlice1 u w *
      (evenCompactGapReflectedTwelveSlice1 u w + evenCompactGapCorrectionSlice1 u) +
    evenCompactGapHeadSlice2 u w *
      (evenCompactGapReflectedTwelveSlice0 u w + evenCompactGapCorrectionSlice0 u)

theorem evenCompactGapCofactorTerm0_coeff_two_factored (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 2 =
      evenCompactGapCofactorTerm0Slice2Factored u w := by
  unfold evenCompactGapCofactorTerm0 evenCompactGapCofactorTerm0Slice2Factored
  rw [evenCompactGapCoeff_mul_2]
  simp only [Polynomial.coeff_add, evenCompactGapHeadPolynomial_coeff_slice0,
    evenCompactGapHeadPolynomial_coeff_slice1, evenCompactGapHeadPolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapCorrectionPolynomial_coeff_slice0,
    evenCompactGapCorrectionPolynomial_coeff_slice1,
    evenCompactGapCorrectionPolynomial_coeff_slice2]

/-- Normalized corrected leading contribution; its incidence is proved below. -/
def evenCompactGapCofactorTerm0Slice2 (u w : ℝ) : ℝ :=
  compactGapNormalize% ring_nf =>
    (dsimp% only [evenCompactGapCofactorTerm0Slice2Factored,
      evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2,
      evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2, evenCompactGapCorrectionSlice0,
      evenCompactGapCorrectionSlice1, evenCompactGapCorrectionSlice2,
      evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1]
      (evenCompactGapCofactorTerm0Slice2Factored u w))

/-- Complete leading contribution at degree two, retaining the correction. -/
theorem evenCompactGapCofactorTerm0_coeff_slice2 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 2 = evenCompactGapCofactorTerm0Slice2 u w := by
  rw [evenCompactGapCofactorTerm0_coeff_two_factored]
  dsimp only [evenCompactGapCofactorTerm0Slice2Factored,
    evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2,
    evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
    evenCompactGapReflectedTwelveSlice2, evenCompactGapCorrectionSlice0,
    evenCompactGapCorrectionSlice1, evenCompactGapCorrectionSlice2,
    evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1,
    evenCompactGapCofactorTerm0Slice2]
  ring1

end
end HTGeometry
