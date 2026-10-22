import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm0Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm1Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm2Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm3Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm4Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm5Slice4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTerm6Slice4

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Degree four assembled from independently checked cofactor identities. -/
theorem evenCompactGapDetPolynomial_coeff_four (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 4 = evenCompactRawGapGrade4 u w := by
  rw [evenCompactGapDetPolynomial_cofactor_eq]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_add,
    evenCompactGapCofactorTerm0_coeff_slice4,
    evenCompactGapCofactorTerm1_coeff_slice4,
    evenCompactGapCofactorTerm2_coeff_slice4,
    evenCompactGapCofactorTerm3_coeff_slice4,
    evenCompactGapCofactorTerm4_coeff_slice4,
    evenCompactGapCofactorTerm5_coeff_slice4,
    evenCompactGapCofactorTerm6_coeff_slice4]
  unfold evenCompactRawGapGrade4 evenCompactGapCofactorTerm0Slice4 evenCompactGapCofactorTerm1Slice4 evenCompactGapCofactorTerm2Slice4 evenCompactGapCofactorTerm3Slice4 evenCompactGapCofactorTerm4Slice4 evenCompactGapCofactorTerm5Slice4 evenCompactGapCofactorTerm6Slice4
  dsimp only [evenCompactGapCofactorTerm4Slice4Certificate,
    evenCompactGapCofactorTerm5Slice4Certificate, evenCompactGapCofactorTerm6Slice4Certificate]
  ring1

end
end HTGeometry
