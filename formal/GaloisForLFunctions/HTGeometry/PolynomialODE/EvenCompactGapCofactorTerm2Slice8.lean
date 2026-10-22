import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry

noncomputable section

/-- Certified coefficients of the two factor polynomials needed at slice eight. -/
def evenCompactGapCofactorTerm2LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
      evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)

def evenCompactGapCofactorTerm2RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)

/-- Factorized normal form for adjugate contribution 2 at gap degree eight. -/
def evenCompactGapCofactorTerm2Slice8 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm2LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm2RightSlice0Certificate u w).value)

theorem evenCompactGapCofactorTerm2_coeff_slice8 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 8 = evenCompactGapCofactorTerm2Slice8 u w := by
  unfold evenCompactGapCofactorTerm2 evenCompactGapCofactorTerm2Slice8
  have hfactor :
      2 *
          (evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
            evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) *
          evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w =
        Polynomial.C (2 : ℝ) *
          ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
            evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) *
            (evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w)) := by
    have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) := by
      exact (Polynomial.C_eq_natCast 2).symm
    rw [htwo]
    ring
  rw [hfactor]
  rw [Polynomial.coeff_C_mul, evenCompactGapCoeff_mul_8]
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
    (evenCompactGapCofactorTerm2RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightSlice8Certificate u w).eq_value]

end

end HTGeometry
