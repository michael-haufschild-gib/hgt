import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTopNormalizer

namespace HTGeometry

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- Certified coefficients of the two factor polynomials needed at slice 11. -/
def evenCompactGapCofactorTerm1LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1LeftSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)
def evenCompactGapCofactorTerm1LeftSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10)
def evenCompactGapCofactorTerm1LeftSlice11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11)

def evenCompactGapCofactorTerm1RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1RightSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)
def evenCompactGapCofactorTerm1RightSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10)
def evenCompactGapCofactorTerm1RightSlice11Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11)

/-- Factorized normal form for adjugate contribution 1 at gap degree 11. -/
def evenCompactGapCofactorTerm1Slice11 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice11Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice10Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice9Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice9Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice10Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice11Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice0Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice11 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 11 = evenCompactGapCofactorTerm1Slice11 u w := by
  unfold evenCompactGapCofactorTerm1 evenCompactGapCofactorTerm1Slice11
  rw [evenCompactGapCoeff_mul_11]
  simp only [
    (evenCompactGapCofactorTerm1LeftSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftSlice11Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice11Certificate u w).eq_value]

end

end HTGeometry
