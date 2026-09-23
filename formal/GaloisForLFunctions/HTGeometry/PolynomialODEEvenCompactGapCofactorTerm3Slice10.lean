import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm3FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 3 at gap degree 10. -/
def evenCompactGapCofactorTerm3Slice10 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm3LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff10Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm3LeftFactorCoeff10Certificate u w).value *
      (evenCompactGapCofactorTerm3RightFactorCoeff0Certificate u w).value)

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
    (evenCompactGapCofactorTerm3LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3LeftFactorCoeff10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm3RightFactorCoeff10Certificate u w).eq_value]

end

end HTGeometry
