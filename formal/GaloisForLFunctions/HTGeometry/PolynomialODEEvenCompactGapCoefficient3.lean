import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm0Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm1Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm2Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm3Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm4Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm5Slice3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm6Slice3

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Degree three assembled from independently checked cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_three (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 3 = evenCompactRawGapGrade3 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice3,
    evenCompactGapCofactorTerm1_coeff_slice3,
    evenCompactGapCofactorTerm2_coeff_slice3,
    evenCompactGapCofactorTerm3_coeff_slice3,
    evenCompactGapCofactorTerm4_coeff_slice3,
    evenCompactGapCofactorTerm5_coeff_slice3,
    evenCompactGapCofactorTerm6_coeff_slice3]
  unfold evenCompactRawGapGrade3 evenCompactGapCofactorTerm0Slice3 evenCompactGapCofactorTerm1Slice3 evenCompactGapCofactorTerm2Slice3 evenCompactGapCofactorTerm3Slice3 evenCompactGapCofactorTerm4Slice3 evenCompactGapCofactorTerm5Slice3 evenCompactGapCofactorTerm6Slice3
  ring1

end
end HTGeometry
