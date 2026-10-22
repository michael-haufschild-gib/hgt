import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm6FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 6 at gap degree 9. -/
def evenCompactGapCofactorTerm6Slice9 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm6LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm6LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm6RightFactorCoeff0Certificate u w).value

theorem evenCompactGapCofactorTerm6_coeff_slice9 (u w : ℝ) :
    (evenCompactGapCofactorTerm6 u w).coeff 9 = evenCompactGapCofactorTerm6Slice9 u w := by
  unfold evenCompactGapCofactorTerm6 evenCompactGapCofactorTerm6Slice9
  rw [evenCompactGapCoeff_mul_9]
  simp only [
    (evenCompactGapCofactorTerm6LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm6RightFactorCoeff9Certificate u w).eq_value]

end

end HTGeometry
