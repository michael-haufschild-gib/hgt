import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry

noncomputable section

/-- Certified coefficients of the two factor polynomials needed at slice eight. -/
def evenCompactGapCofactorTerm6LeftSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm6LeftSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm6LeftSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm6LeftSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm6LeftSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm6LeftSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm6LeftSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm6LeftSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm6LeftSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorHigherCertified% (((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ) * evenCompactGapReflectedFourPolynomial u w -
      (evenCompactGapReflectedTwoPolynomial u w)^(2 : ℕ)).coeff 8)

def evenCompactGapCofactorTerm6RightSlice0Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 0) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, Polynomial.mul_coeff_zero]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0]
def evenCompactGapCofactorTerm6RightSlice1Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 1) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, Polynomial.mul_coeff_one]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1]
def evenCompactGapCofactorTerm6RightSlice2Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 2) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_2]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2]
def evenCompactGapCofactorTerm6RightSlice3Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 3) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_3]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3]
def evenCompactGapCofactorTerm6RightSlice4Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 4) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice4 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice4 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_4]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4]
def evenCompactGapCofactorTerm6RightSlice5Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 5) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice5 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice4 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice4 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice5 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_5]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5]
def evenCompactGapCofactorTerm6RightSlice6Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 6) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice6 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice5 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice4 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice4 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice5 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice6 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_6]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5,
      evenCompactGapReflectedTenPolynomial_coeff_slice6]
def evenCompactGapCofactorTerm6RightSlice7Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 7) where
  value := evenCompactGapReflectedTenSlice0 u w * evenCompactGapReflectedTenSlice7 u w +
    evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice6 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice5 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice4 u w +
    evenCompactGapReflectedTenSlice4 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice5 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice6 u w * evenCompactGapReflectedTenSlice1 u w +
    evenCompactGapReflectedTenSlice7 u w * evenCompactGapReflectedTenSlice0 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_7]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5,
      evenCompactGapReflectedTenPolynomial_coeff_slice6,
      evenCompactGapReflectedTenPolynomial_coeff_slice7]
def evenCompactGapCofactorTerm6RightSlice8Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedTenPolynomial u w)^(2 : ℕ)).coeff 8) where
  value := evenCompactGapReflectedTenSlice1 u w * evenCompactGapReflectedTenSlice7 u w +
    evenCompactGapReflectedTenSlice2 u w * evenCompactGapReflectedTenSlice6 u w +
    evenCompactGapReflectedTenSlice3 u w * evenCompactGapReflectedTenSlice5 u w +
    evenCompactGapReflectedTenSlice4 u w * evenCompactGapReflectedTenSlice4 u w +
    evenCompactGapReflectedTenSlice5 u w * evenCompactGapReflectedTenSlice3 u w +
    evenCompactGapReflectedTenSlice6 u w * evenCompactGapReflectedTenSlice2 u w +
    evenCompactGapReflectedTenSlice7 u w * evenCompactGapReflectedTenSlice1 u w
  eq_value := by
    rw [pow_two, evenCompactGapCoeff_mul_8]
    rw [evenCompactGapReflectedTenPolynomial_coeff_above u w 8 (by norm_num)]
    simp only [evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5,
      evenCompactGapReflectedTenPolynomial_coeff_slice6,
      evenCompactGapReflectedTenPolynomial_coeff_slice7,
      zero_mul, mul_zero, zero_add, add_zero]

/-- Factorized normal form for adjugate contribution 1 at gap degree eight. -/
def evenCompactGapCofactorTerm6Slice8 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm6LeftSlice0Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice8Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice1Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice7Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice2Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice6Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice3Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice5Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice4Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice4Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice5Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice3Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice6Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice2Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice7Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice1Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftSlice8Certificate u w).value *
      (evenCompactGapCofactorTerm6RightSlice0Certificate u w).value

theorem evenCompactGapCofactorTerm6_coeff_slice8 (u w : ℝ) :
    (evenCompactGapCofactorTerm6 u w).coeff 8 = evenCompactGapCofactorTerm6Slice8 u w := by
  unfold evenCompactGapCofactorTerm6 evenCompactGapCofactorTerm6Slice8
  rw [evenCompactGapCoeff_mul_8]
  simp only [
    (evenCompactGapCofactorTerm6LeftSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftSlice8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightSlice8Certificate u w).eq_value]

end

end HTGeometry
