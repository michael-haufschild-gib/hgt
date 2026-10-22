import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice0
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice1
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice3
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCorrectionSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapScalarNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Exact cubic convolution with the complete quadratic correction retained. -/
def evenCompactGapCofactorTerm0Slice3Factored (u w : ℝ) : ℝ :=
  evenCompactGapHeadSlice0 u w * evenCompactGapReflectedTwelveSlice3 u w +
    evenCompactGapHeadSlice1 u w *
      (evenCompactGapReflectedTwelveSlice2 u w + evenCompactGapCorrectionSlice2 u) +
    evenCompactGapHeadSlice2 u w *
      (evenCompactGapReflectedTwelveSlice1 u w + evenCompactGapCorrectionSlice1 u) +
    evenCompactGapHeadSlice3 u w *
      (evenCompactGapReflectedTwelveSlice0 u w + evenCompactGapCorrectionSlice0 u)

theorem evenCompactGapCofactorTerm0_coeff_three_factored (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 3 =
      evenCompactGapCofactorTerm0Slice3Factored u w := by
  have hcorr : (evenCompactGapCorrectionPolynomial u).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega))
  unfold evenCompactGapCofactorTerm0 evenCompactGapCofactorTerm0Slice3Factored
  rw [evenCompactGapCoeff_mul_3]
  simp only [Polynomial.coeff_add, evenCompactGapHeadPolynomial_coeff_slice0,
    evenCompactGapHeadPolynomial_coeff_slice1, evenCompactGapHeadPolynomial_coeff_slice2,
    evenCompactGapHeadPolynomial_coeff_slice3,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
    evenCompactGapCorrectionPolynomial_coeff_slice0,
    evenCompactGapCorrectionPolynomial_coeff_slice1,
    evenCompactGapCorrectionPolynomial_coeff_slice2, hcorr, add_zero]

/-- Normalized corrected leading contribution; independently verified below. -/
def evenCompactGapCofactorTerm0Slice3 (u w : ℝ) : ℝ :=
  compactGapNormalize% ring_nf =>
    (dsimp% only [evenCompactGapCofactorTerm0Slice3Factored,
      evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2,
      evenCompactGapHeadSlice3,
      evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2, evenCompactGapReflectedTwelveSlice3,
      evenCompactGapCorrectionSlice0, evenCompactGapCorrectionSlice1,
      evenCompactGapCorrectionSlice2,
      evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1]
      (evenCompactGapCofactorTerm0Slice3Factored u w))

/-- Complete corrected leading contribution at degree three. -/
theorem evenCompactGapCofactorTerm0_coeff_slice3 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 3 = evenCompactGapCofactorTerm0Slice3 u w := by
  rw [evenCompactGapCofactorTerm0_coeff_three_factored]
  dsimp only [evenCompactGapCofactorTerm0Slice3Factored,
    evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2,
    evenCompactGapHeadSlice3,
    evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
    evenCompactGapReflectedTwelveSlice2, evenCompactGapReflectedTwelveSlice3,
    evenCompactGapCorrectionSlice0, evenCompactGapCorrectionSlice1,
    evenCompactGapCorrectionSlice2,
    evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1,
    evenCompactGapCofactorTerm0Slice3]
  ring1

end
end HTGeometry
