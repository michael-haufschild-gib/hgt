import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm5FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 5 at gap degree 9. -/
def evenCompactGapCofactorTerm5Slice9 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm5LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm5LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm5RightFactorCoeff0Certificate u w).value)

theorem evenCompactGapCofactorTerm5_coeff_slice9 (u w : ℝ) :
    (evenCompactGapCofactorTerm5 u w).coeff 9 = evenCompactGapCofactorTerm5Slice9 u w := by
  unfold evenCompactGapCofactorTerm5 evenCompactGapCofactorTerm5Slice9
  have hfactor :
      2 * (evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedFourPolynomial u w - ((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ)) * evenCompactGapReflectedSixPolynomial u w) * evenCompactGapReflectedEightPolynomial u w * evenCompactGapReflectedTenPolynomial u w =
        Polynomial.C (2 : ℝ) * ((evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedFourPolynomial u w - ((evenCompactGapSourceZeroPolynomial u)^(2 : ℕ)) * evenCompactGapReflectedSixPolynomial u w) * (evenCompactGapReflectedEightPolynomial u w * evenCompactGapReflectedTenPolynomial u w)) := by
    have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) :=
      (Polynomial.C_eq_natCast 2).symm
    rw [htwo]
    ring
  rw [hfactor]
  rw [Polynomial.coeff_C_mul, evenCompactGapCoeff_mul_9]
  simp only [
    (evenCompactGapCofactorTerm5LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm5RightFactorCoeff9Certificate u w).eq_value]

end

end HTGeometry
