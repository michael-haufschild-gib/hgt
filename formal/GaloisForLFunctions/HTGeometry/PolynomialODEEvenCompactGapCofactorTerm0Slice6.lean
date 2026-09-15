import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice0
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice1
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice2
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice4
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHeadSlice6
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCorrectionSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCertifiedNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Degree-six convolution of the leading cofactor with the full quadratic correction. -/
def evenCompactGapCofactorTerm0Slice6Factored (u w : ℝ) : ℝ :=
  evenCompactGapHeadSlice0 u w * evenCompactGapReflectedTwelveSlice6 u w +
    evenCompactGapHeadSlice1 u w * evenCompactGapReflectedTwelveSlice5 u w +
    evenCompactGapHeadSlice2 u w * evenCompactGapReflectedTwelveSlice4 u w +
    evenCompactGapHeadSlice3 u w * evenCompactGapReflectedTwelveSlice3 u w +
    evenCompactGapHeadSlice4 u w *
      (evenCompactGapReflectedTwelveSlice2 u w + evenCompactGapCorrectionSlice2 u) +
    evenCompactGapHeadSlice5 u w *
      (evenCompactGapReflectedTwelveSlice1 u w + evenCompactGapCorrectionSlice1 u) +
    evenCompactGapHeadSlice6 u w *
      (evenCompactGapReflectedTwelveSlice0 u w + evenCompactGapCorrectionSlice0 u)

theorem evenCompactGapCofactorTerm0_coeff_six_factored (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 6 =
      evenCompactGapCofactorTerm0Slice6Factored u w := by
  have hcorr3 : (evenCompactGapCorrectionPolynomial u).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega))
  have hcorr4 : (evenCompactGapCorrectionPolynomial u).coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega))
  have hcorr5 : (evenCompactGapCorrectionPolynomial u).coeff 5 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega))
  have hcorr6 : (evenCompactGapCorrectionPolynomial u).coeff 6 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt (by omega))
  unfold evenCompactGapCofactorTerm0 evenCompactGapCofactorTerm0Slice6Factored
  rw [evenCompactGapCoeff_mul_6]
  simp only [Polynomial.coeff_add, evenCompactGapHeadPolynomial_coeff_slice0,
    evenCompactGapHeadPolynomial_coeff_slice1, evenCompactGapHeadPolynomial_coeff_slice2,
    evenCompactGapHeadPolynomial_coeff_slice3, evenCompactGapHeadPolynomial_coeff_slice4,
    evenCompactGapHeadPolynomial_coeff_slice5, evenCompactGapHeadPolynomial_coeff_slice6,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
    evenCompactGapCorrectionPolynomial_coeff_slice0,
    evenCompactGapCorrectionPolynomial_coeff_slice1,
    evenCompactGapCorrectionPolynomial_coeff_slice2,
    hcorr3, hcorr4, hcorr5, hcorr6, add_zero]

/-- Normalized leading contribution at degree six, retaining its equality certificate. -/
def evenCompactGapCofactorTerm0Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm (evenCompactGapCofactorTerm0Slice6Factored u w) :=
  compactGapCertified% (
    dsimp only [evenCompactGapCofactorTerm0Slice6Factored,
      evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2,
      evenCompactGapHeadSlice3, evenCompactGapHeadSlice4, evenCompactGapHeadSlice5,
      evenCompactGapHeadSlice6, evenCompactGapHeadSlice5Certificate,
      evenCompactGapHeadSlice6Certificate,
      evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2, evenCompactGapReflectedTwelveSlice3,
      evenCompactGapReflectedTwelveSlice4, evenCompactGapReflectedTwelveSlice5,
      evenCompactGapReflectedTwelveSlice6,
      evenCompactGapCorrectionSlice0, evenCompactGapCorrectionSlice1,
      evenCompactGapCorrectionSlice2,
      evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1]
    ring_nf) => (evenCompactGapCofactorTerm0Slice6Factored u w)

def evenCompactGapCofactorTerm0Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm0Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm0_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 6 = evenCompactGapCofactorTerm0Slice6 u w := by
  rw [evenCompactGapCofactorTerm0_coeff_six_factored]
  exact (evenCompactGapCofactorTerm0Slice6Certificate u w).eq_value

end
end HTGeometry
