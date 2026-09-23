import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTopNormalizer

namespace HTGeometry

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- Certified coefficients of the two factor polynomials needed at slice 11. -/
def evenCompactGapCofactorTerm2LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)
def evenCompactGapCofactorTerm2LeftSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9)
def evenCompactGapCofactorTerm2LeftSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10)
def evenCompactGapCofactorTerm2LeftSlice11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11)

def evenCompactGapCofactorTerm2RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)
def evenCompactGapCofactorTerm2RightSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9)
def evenCompactGapCofactorTerm2RightSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10)
def evenCompactGapCofactorTerm2RightSlice11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11)

/-- Factorized normal form for adjugate contribution 2 at gap degree 11. -/
def evenCompactGapCofactorTerm2Slice11 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm2LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice11Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice10Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice9Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice9Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice10Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice11Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice0Certificate u w).value)

theorem evenCompactGapCofactorTerm2_coeff_slice11 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 11 = evenCompactGapCofactorTerm2Slice11 u w := by
  unfold evenCompactGapCofactorTerm2 evenCompactGapCofactorTerm2Slice11
  have hfactor :
      2 * (evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) * evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w =
        Polynomial.C (2 : ℝ) * ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) * (evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w)) := by
    have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) :=
      (Polynomial.C_eq_natCast 2).symm
    rw [htwo]
    ring
  rw [hfactor]
  rw [Polynomial.coeff_C_mul, evenCompactGapCoeff_mul_11]
  simp only [
    (evenCompactGapCofactorTerm2LeftSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftSlice11Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice11Certificate u w).eq_value]

end

end HTGeometry
