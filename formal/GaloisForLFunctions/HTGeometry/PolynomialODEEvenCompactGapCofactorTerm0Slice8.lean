import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry

noncomputable section

/-- Normalized leading-adjugate contribution at gap degree eight, with its exact certificate. -/
def evenCompactGapCofactorTerm0Slice8Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm0 u w).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm0 u w).coeff 8)

def evenCompactGapCofactorTerm0Slice8 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm0Slice8Certificate u w).value

theorem evenCompactGapCofactorTerm0_coeff_slice8 (u w : ℝ) :
    (evenCompactGapCofactorTerm0 u w).coeff 8 = evenCompactGapCofactorTerm0Slice8 u w :=
  (evenCompactGapCofactorTerm0Slice8Certificate u w).eq_value

end

end HTGeometry
