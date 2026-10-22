import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 3 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm3Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm3 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm3 u w).coeff 6)

def evenCompactGapCofactorTerm3Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm3Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm3_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm3 u w).coeff 6 = evenCompactGapCofactorTerm3Slice6 u w :=
  (evenCompactGapCofactorTerm3Slice6Certificate u w).eq_value

end
end HTGeometry
