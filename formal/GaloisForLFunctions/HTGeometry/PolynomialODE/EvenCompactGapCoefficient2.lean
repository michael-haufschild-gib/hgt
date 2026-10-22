import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm0Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm1Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm2Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm3Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm4Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm5Slice2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm6Slice2

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Degree two assembled from independently checked cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_two (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 2 = evenCompactRawGapGrade2 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice2,
    evenCompactGapCofactorTerm1_coeff_slice2,
    evenCompactGapCofactorTerm2_coeff_slice2,
    evenCompactGapCofactorTerm3_coeff_slice2,
    evenCompactGapCofactorTerm4_coeff_slice2,
    evenCompactGapCofactorTerm5_coeff_slice2,
    evenCompactGapCofactorTerm6_coeff_slice2]
  unfold evenCompactRawGapGrade2 evenCompactGapCofactorTerm0Slice2 evenCompactGapCofactorTerm1Slice2 evenCompactGapCofactorTerm2Slice2 evenCompactGapCofactorTerm3Slice2 evenCompactGapCofactorTerm4Slice2 evenCompactGapCofactorTerm5Slice2 evenCompactGapCofactorTerm6Slice2
  ring1

end
end HTGeometry
