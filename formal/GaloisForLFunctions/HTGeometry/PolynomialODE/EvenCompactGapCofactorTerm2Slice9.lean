import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm2FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 2 at gap degree 9. -/
def evenCompactGapCofactorTerm2Slice9 (u w : ℝ) : ℝ :=
  2 * ((evenCompactGapCofactorTerm2LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm2LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm2RightFactorCoeff0Certificate u w).value)

theorem evenCompactGapCofactorTerm2_coeff_slice9 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 9 = evenCompactGapCofactorTerm2Slice9 u w := by
  unfold evenCompactGapCofactorTerm2 evenCompactGapCofactorTerm2Slice9
  have hfactor :
      2 * (evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) * evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w =
        Polynomial.C (2 : ℝ) * ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) * (evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w)) := by
    have htwo : (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) :=
      (Polynomial.C_eq_natCast 2).symm
    rw [htwo]
    ring
  rw [hfactor]
  rw [Polynomial.coeff_C_mul, evenCompactGapCoeff_mul_9]
  simp only [
    (evenCompactGapCofactorTerm2LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm2RightFactorCoeff9Certificate u w).eq_value]

end

end HTGeometry
