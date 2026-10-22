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
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice10
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapHeadSlice11
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCorrectionSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCertifiedNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 20000

/-- Degree-11 convolution of the leading cofactor with the full quadratic correction. -/
def evenCompactGapCofactorTerm0Slice11Factored (u w : ℝ) : ℝ :=
  evenCompactGapHeadSlice3 u w * evenCompactGapReflectedTwelveSlice8 u w +
    evenCompactGapHeadSlice4 u w * evenCompactGapReflectedTwelveSlice7 u w +
    evenCompactGapHeadSlice5 u w * evenCompactGapReflectedTwelveSlice6 u w +
    evenCompactGapHeadSlice6 u w * evenCompactGapReflectedTwelveSlice5 u w +
    evenCompactGapHeadSlice7 u w * evenCompactGapReflectedTwelveSlice4 u w +
    evenCompactGapHeadSlice8 u w * evenCompactGapReflectedTwelveSlice3 u w +
    evenCompactGapHeadSlice9 u w *
      (evenCompactGapReflectedTwelveSlice2 u w + evenCompactGapCorrectionSlice2 u) +
    evenCompactGapHeadSlice10 u w *
      (evenCompactGapReflectedTwelveSlice1 u w + evenCompactGapCorrectionSlice1 u) +
    evenCompactGapHeadSlice11 u w *
      (evenCompactGapReflectedTwelveSlice0 u w + evenCompactGapCorrectionSlice0 u)

theorem evenCompactGapCofactorTerm0_coeff_11_factored (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 11 =
      evenCompactGapCofactorTerm0Slice11Factored u w := by
  have hcorr (n : ℕ) (hn : 2 < n) :
      (evenCompactGapCorrectionPolynomial u).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt hn)
  have htw9 : (evenCompactGapReflectedTwelvePolynomial u w).coeff 9 = 0 :=
    evenCompactGapReflectedTwelvePolynomial_coeff_above u w 9 (by omega)
  have htw10 : (evenCompactGapReflectedTwelvePolynomial u w).coeff 10 = 0 :=
    evenCompactGapReflectedTwelvePolynomial_coeff_above u w 10 (by omega)
  have htw11 : (evenCompactGapReflectedTwelvePolynomial u w).coeff 11 = 0 :=
    evenCompactGapReflectedTwelvePolynomial_coeff_above u w 11 (by omega)
  unfold evenCompactGapCofactorTerm0 evenCompactGapCofactorTerm0Slice11Factored
  rw [evenCompactGapCoeff_mul_11]
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
    evenCompactGapHeadPolynomial_coeff_slice10,
    evenCompactGapHeadPolynomial_coeff_slice11,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice7,
    evenCompactGapReflectedTwelvePolynomial_coeff_slice8,
    htw9, htw10, htw11,
    evenCompactGapCorrectionPolynomial_coeff_slice0,
    evenCompactGapCorrectionPolynomial_coeff_slice1,
    evenCompactGapCorrectionPolynomial_coeff_slice2,
    hcorr 3 (by omega), hcorr 4 (by omega), hcorr 5 (by omega), hcorr 6 (by omega), hcorr 7 (by omega), hcorr 8 (by omega), hcorr 9 (by omega), hcorr 10 (by omega), hcorr 11 (by omega), add_zero, mul_zero, zero_add]

/-- Normalized leading contribution at degree 11, retaining its equality certificate. -/
def evenCompactGapCofactorTerm0Slice11Certificate (u w : ℝ) :
    CompactGapNormalForm (evenCompactGapCofactorTerm0Slice11Factored u w) :=
  compactGapCertified% (
    dsimp only [evenCompactGapCofactorTerm0Slice11Factored,
      evenCompactGapHeadSlice0, evenCompactGapHeadSlice1, evenCompactGapHeadSlice2, evenCompactGapHeadSlice3, evenCompactGapHeadSlice4, evenCompactGapHeadSlice5, evenCompactGapHeadSlice6, evenCompactGapHeadSlice7, evenCompactGapHeadSlice8, evenCompactGapHeadSlice9, evenCompactGapHeadSlice10, evenCompactGapHeadSlice11,
      evenCompactGapHeadSlice5Certificate, evenCompactGapHeadSlice6Certificate, evenCompactGapHeadSlice7Certificate, evenCompactGapHeadSlice8Certificate, evenCompactGapHeadSlice9Certificate, evenCompactGapHeadSlice10Certificate, evenCompactGapHeadSlice11Certificate,
      evenCompactGapReflectedTwelveSlice0, evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2, evenCompactGapReflectedTwelveSlice3,
      evenCompactGapReflectedTwelveSlice4, evenCompactGapReflectedTwelveSlice5,
      evenCompactGapReflectedTwelveSlice6, evenCompactGapReflectedTwelveSlice7,
      evenCompactGapReflectedTwelveSlice8,
      evenCompactGapCorrectionSlice0, evenCompactGapCorrectionSlice1,
      evenCompactGapCorrectionSlice2,
      evenCompactGapSourceZeroSlice0, evenCompactGapSourceZeroSlice1]
    ring_nf) => (evenCompactGapCofactorTerm0Slice11Factored u w)

def evenCompactGapCofactorTerm0Slice11 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm0Slice11Certificate u w).value

theorem evenCompactGapCofactorTerm0_coeff_slice11 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 11 = evenCompactGapCofactorTerm0Slice11 u w := by
  rw [evenCompactGapCofactorTerm0_coeff_11_factored]
  exact (evenCompactGapCofactorTerm0Slice11Certificate u w).eq_value

end
end HTGeometry
