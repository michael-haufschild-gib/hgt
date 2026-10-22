import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 4 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm4Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm4 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm4 u w).coeff 6)

def evenCompactGapCofactorTerm4Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm4Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm4_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm4 u w).coeff 6 = evenCompactGapCofactorTerm4Slice6 u w :=
  (evenCompactGapCofactorTerm4Slice6Certificate u w).eq_value

end
end HTGeometry
