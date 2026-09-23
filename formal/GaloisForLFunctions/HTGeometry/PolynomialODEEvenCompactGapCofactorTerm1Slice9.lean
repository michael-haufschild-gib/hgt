import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- Certified coefficients of the two factor polynomials needed at slice 9. -/
def evenCompactGapCofactorTerm1LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1LeftSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)

def evenCompactGapCofactorTerm1RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1RightSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorHigherCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)

/-- Factorized normal form for adjugate contribution 1 at gap degree 9. -/
def evenCompactGapCofactorTerm1Slice9 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice9Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftSlice9Certificate u w).value *
      (evenCompactGapCofactorTerm1RightSlice0Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice9 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 9 = evenCompactGapCofactorTerm1Slice9 u w := by
  unfold evenCompactGapCofactorTerm1 evenCompactGapCofactorTerm1Slice9
  rw [evenCompactGapCoeff_mul_9]
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
    (evenCompactGapCofactorTerm1RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightSlice9Certificate u w).eq_value]

end

end HTGeometry
