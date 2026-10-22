import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice0
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice1
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice3
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice5
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice7
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice8
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice9
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCorrectionSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCertifiedNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 20000

/-- Degree-9 convolution of the leading cofactor with the full quadratic correction. -/
def evenCompactGapCofactorTerm0Slice9Factored (u w : ℝ) : ℝ :=
  evenCompactGapHeadSlice1 u w * evenCompactGapReflectedTwelveSlice8 u w +
    evenCompactGapHeadSlice2 u w * evenCompactGapReflectedTwelveSlice7 u w +
    evenCompactGapHeadSlice3 u w * evenCompactGapReflectedTwelveSlice6 u w +
    evenCompactGapHeadSlice4 u w * evenCompactGapReflectedTwelveSlice5 u w +
    evenCompactGapHeadSlice5 u w * evenCompactGapReflectedTwelveSlice4 u w +
    evenCompactGapHeadSlice6 u w * evenCompactGapReflectedTwelveSlice3 u w +
    evenCompactGapHeadSlice7 u w *
      (evenCompactGapReflectedTwelveSlice2 u w + evenCompactGapCorrectionSlice2 u) +
    evenCompactGapHeadSlice8 u w *
      (evenCompactGapReflectedTwelveSlice1 u w + evenCompactGapCorrectionSlice1 u) +
    evenCompactGapHeadSlice9 u w *
      (evenCompactGapReflectedTwelveSlice0 u w + evenCompactGapCorrectionSlice0 u)

theorem evenCompactGapCofactorTerm0_coeff_9_factored (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 9 =
      evenCompactGapCofactorTerm0Slice9Factored u w := by
  have hcorr (n : ℕ) (hn : 2 < n) :
      (evenCompactGapCorrectionPolynomial u).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt hn)
  have htw9 : (evenCompactGapReflectedTwelvePolynomial u w).coeff 9 = 0 :=
    evenCompactGapReflectedTwelvePolynomial_coeff_above u w 9 (by omega)
  unfold evenCompactGapCofactorTerm0 evenCompactGapCofactorTerm0Slice9Factored
  rw [evenCompactGapCoeff_mul_9]
  simp only [Polynomial.coeff_add,
    evenCompactGapHeadPolynomial_coeff_slice0,
    evenCompactGapHeadPolynomial_coeff_slice1,
    evenCompactGapHeadPolynomial_coeff_slice2,
    evenCompactGapHeadPolynomial_coeff_slice3,
    evenCompactGapHeadPolynomial_coeff_slice4,
    evenCompactGapHeadPolynomial_coeff_slice5,
    evenCompactGapHeadPolynomial_coeff_slice6,
    evenCompactGapHeadPolynomial_coeff_slice7,
    evenCompactGapHeadPolynomial_coeff_slice8,
    evenCompactGapHeadPolynomial_coeff_slice9,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice7,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice8,
    htw9,
    evenCompactGapCorrectionPolynomial_coeff_slice0,
    evenCompactGapCorrectionPolynomial_coeff_slice1,
    evenCompactGapCorrectionPolynomial_coeff_slice2,
    hcorr 3 (by omega), hcorr 4 (by omega), hcorr 5 (by omega), hcorr 6 (by omega), hcorr 7 (by omega), hcorr 8 (by omega), hcorr 9 (by omega), add_zero, mul_zero, zero_add]

/-- Normalized leading contribution at degree 9, retaining its equality certificate. -/
def evenCompactGapCofactorTerm0Slice9Certificate (u w : ℝ) :
    CompactGapNormalForm (evenCompactGapCofactorTerm0Slice9Factored u w) :=
  compactGapCertified% (
    dsimp only [evenCompactGapCofactorTerm0Slice9Factored,
      evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2, evenCompactGapHeadSlice3, evenCompactGapHeadSlice4, evenCompactGapHeadSlice5, evenCompactGapHeadSlice6, evenCompactGapHeadSlice7, evenCompactGapHeadSlice8, evenCompactGapHeadSlice9,
      evenCompactGapHeadSlice5Certificate, evenCompactGapHeadSlice6Certificate, evenCompactGapHeadSlice7Certificate, evenCompactGapHeadSlice8Certificate, evenCompactGapHeadSlice9Certificate,
      evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2, evenCompactGapReflectedTwelveSlice3,
      evenCompactGapReflectedTwelveSlice4, evenCompactGapReflectedTwelveSlice5,
      evenCompactGapReflectedTwelveSlice6, evenCompactGapReflectedTwelveSlice7,
      evenCompactGapReflectedTwelveSlice8,
      evenCompactGapCorrectionSlice0, evenCompactGapCorrectionSlice1,
      evenCompactGapCorrectionSlice2,
      evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1]
    ring_nf) => (evenCompactGapCofactorTerm0Slice9Factored u w)

def evenCompactGapCofactorTerm0Slice9 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm0Slice9Certificate u w).value

theorem evenCompactGapCofactorTerm0_coeff_slice9 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 9 = evenCompactGapCofactorTerm0Slice9 u w := by
  rw [evenCompactGapCofactorTerm0_coeff_9_factored]
  exact (evenCompactGapCofactorTerm0Slice9Certificate u w).eq_value

end
end HTGeometry
