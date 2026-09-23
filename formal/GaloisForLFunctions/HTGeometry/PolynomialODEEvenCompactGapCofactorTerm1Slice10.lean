import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm1FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 1 at gap degree 10. -/
def evenCompactGapCofactorTerm1Slice10 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff10Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm1LeftFactorCoeff10Certificate u w).value *
      (evenCompactGapCofactorTerm1RightFactorCoeff0Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice10 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 10 = evenCompactGapCofactorTerm1Slice10 u w := by
  unfold evenCompactGapCofactorTerm1 evenCompactGapCofactorTerm1Slice10
  rw [evenCompactGapCoeff_mul_10]
  simp only [
    (evenCompactGapCofactorTerm1LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1LeftFactorCoeff10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm1RightFactorCoeff10Certificate u w).eq_value]

end

end HTGeometry
