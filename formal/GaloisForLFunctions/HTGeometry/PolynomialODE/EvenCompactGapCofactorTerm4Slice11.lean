import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm4FactorSlices

namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

/-- Factorized normal form for adjugate contribution 4 at gap degree 11. -/
def evenCompactGapCofactorTerm4Slice11 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm4LeftFactorCoeff0Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff11Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff1Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff10Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff2Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff9Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff3Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff8Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff4Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff7Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff5Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff6Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff6Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff5Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff7Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff4Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff8Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff3Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff9Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff2Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff10Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff1Certificate u w).value +
    (evenCompactGapCofactorTerm4LeftFactorCoeff11Certificate u w).value *
      (evenCompactGapCofactorTerm4RightFactorCoeff0Certificate u w).value

theorem evenCompactGapCofactorTerm4_coeff_slice11 (u w : ℝ) :
    (evenCompactGapCofactorTerm4 u w).coeff 11 = evenCompactGapCofactorTerm4Slice11 u w := by
  unfold evenCompactGapCofactorTerm4 evenCompactGapCofactorTerm4Slice11
  rw [evenCompactGapCoeff_mul_11]
  simp only [
    (evenCompactGapCofactorTerm4LeftFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4LeftFactorCoeff11Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff0Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff1Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff2Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff3Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff4Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff5Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff6Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff7Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff8Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff9Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff10Certificate u w).eq_value,
    (evenCompactGapCofactorTerm4RightFactorCoeff11Certificate u w).eq_value]

end

end HTGeometry
