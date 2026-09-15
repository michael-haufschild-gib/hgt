import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm0Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm1Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm2Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm3Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm4Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm5Slice7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorTerm6Slice7

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Degree seven assembled from independently certified cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_seven (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 7 = evenCompactRawGapGrade7 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice7,
    evenCompactGapCofactorTerm1_coeff_slice7,
    evenCompactGapCofactorTerm2_coeff_slice7,
    evenCompactGapCofactorTerm3_coeff_slice7,
    evenCompactGapCofactorTerm4_coeff_slice7,
    evenCompactGapCofactorTerm5_coeff_slice7,
    evenCompactGapCofactorTerm6_coeff_slice7]
  unfold evenCompactRawGapGrade7 evenCompactGapCofactorTerm0Slice7
    evenCompactGapCofactorTerm1Slice7 evenCompactGapCofactorTerm2Slice7
    evenCompactGapCofactorTerm3Slice7 evenCompactGapCofactorTerm4Slice7
    evenCompactGapCofactorTerm5Slice7 evenCompactGapCofactorTerm6Slice7
  dsimp only [evenCompactGapCofactorTerm0Slice7Certificate,
    evenCompactGapCofactorTerm1Slice7Certificate,
    evenCompactGapCofactorTerm2Slice7Certificate,
    evenCompactGapCofactorTerm3Slice7Certificate,
    evenCompactGapCofactorTerm4Slice7Certificate,
    evenCompactGapCofactorTerm5Slice7Certificate,
    evenCompactGapCofactorTerm6Slice7Certificate]
  ring1

end
end HTGeometry
