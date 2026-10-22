import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm0Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm1Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm2Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm3Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm4Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm5Slice6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm6Slice6

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Degree six assembled from independently certified cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_six (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 6 = evenCompactRawGapGrade6 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice6,
    evenCompactGapCofactorTerm1_coeff_slice6,
    evenCompactGapCofactorTerm2_coeff_slice6,
    evenCompactGapCofactorTerm3_coeff_slice6,
    evenCompactGapCofactorTerm4_coeff_slice6,
    evenCompactGapCofactorTerm5_coeff_slice6,
    evenCompactGapCofactorTerm6_coeff_slice6]
  unfold evenCompactRawGapGrade6 evenCompactGapCofactorTerm0Slice6
    evenCompactGapCofactorTerm1Slice6 evenCompactGapCofactorTerm2Slice6
    evenCompactGapCofactorTerm3Slice6 evenCompactGapCofactorTerm4Slice6
    evenCompactGapCofactorTerm5Slice6 evenCompactGapCofactorTerm6Slice6
  dsimp only [evenCompactGapCofactorTerm0Slice6Certificate,
    evenCompactGapCofactorTerm1Slice6Certificate,
    evenCompactGapCofactorTerm2Slice6Certificate,
    evenCompactGapCofactorTerm3Slice6Certificate,
    evenCompactGapCofactorTerm4Slice6Certificate,
    evenCompactGapCofactorTerm5Slice6Certificate,
    evenCompactGapCofactorTerm6Slice6Certificate]
  ring1

end
end HTGeometry
