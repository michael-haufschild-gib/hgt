import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- Certified coefficients of the two factor polynomials needed at slice 10. -/
def evenCompactGapCofactorTerm3LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm3LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm3LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm3LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm3LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm3LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm3LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm3LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm3LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm3LeftSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 9)
def evenCompactGapCofactorTerm3LeftSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 10) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)).coeff 10)

def evenCompactGapCofactorTerm3RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 0) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm3RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 1) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm3RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 2) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm3RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 3) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm3RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 4) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm3RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm3RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm3RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm3RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 8)
def evenCompactGapCofactorTerm3RightSlice9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 9) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 9)
def evenCompactGapCofactorTerm3RightSlice10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 10) :=
  compactGapCofactorHigherCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w).coeff 10)

/-- Factorized normal form for adjugate contribution 3 at gap degree 10. -/
def evenCompactGapCofactorTerm3Slice10 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm3LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice10Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice9Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice9Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftSlice10Certificate u w).value *
      (evenCompactGapCofactorTerm3RightSlice0Certificate u w).value)

theorem evenCompactGapCofactorTerm3_coeff_slice10 (u w : ℝ) :
    (evenCompactGapCofactorTerm3 u w).coeff 10 = evenCompactGapCofactorTerm3Slice10 u w := by
  unfold evenCompactGapCofactorTerm3 evenCompactGapCofactorTerm3Slice10
  have hfactor :
      2 * (evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)) * evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w =
        Polynomial.C (2 : ℝ) * ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w - (evenCompactGapReflectedFourPolynomial u w)^(2 : ℕ)) * (evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w)) := by
    have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) :=
      (Polynomial.C_eq_natCast 2).symm
    rw [htwo]
    ring
  rw [hfactor]
  rw [Polynomial.coeff_C_mul, evenCompactGapCoeff_mul_10]
  simp only [
    (evenCompactGapCofactorTerm3LeftSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftSlice10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightSlice10Certificate u w).eq_value]

end

end HTGeometry
