import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm0Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm1Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm2Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm3Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm4Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm5Slice5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm6Slice5

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Degree five assembled from independently certified cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_five (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 5 = evenCompactRawGapGrade5 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice5,
    evenCompactGapCofactorTerm1_coeff_slice5,
    evenCompactGapCofactorTerm2_coeff_slice5,
    evenCompactGapCofactorTerm3_coeff_slice5,
    evenCompactGapCofactorTerm4_coeff_slice5,
    evenCompactGapCofactorTerm5_coeff_slice5,
    evenCompactGapCofactorTerm6_coeff_slice5]
  unfold evenCompactRawGapGrade5 evenCompactGapCofactorTerm0Slice5
    evenCompactGapCofactorTerm1Slice5 evenCompactGapCofactorTerm2Slice5
    evenCompactGapCofactorTerm3Slice5 evenCompactGapCofactorTerm4Slice5
    evenCompactGapCofactorTerm5Slice5 evenCompactGapCofactorTerm6Slice5
  dsimp only [evenCompactGapCofactorTerm0Slice5Certificate,
    evenCompactGapCofactorTerm1Slice5Certificate,
    evenCompactGapCofactorTerm2Slice5Certificate,
    evenCompactGapCofactorTerm3Slice5Certificate,
    evenCompactGapCofactorTerm4Slice5Certificate,
    evenCompactGapCofactorTerm5Slice5Certificate,
    evenCompactGapCofactorTerm6Slice5Certificate]
  ring1

end
end HTGeometry
