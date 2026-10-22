import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 2 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm2Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm2 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm2 u w).coeff 6)

def evenCompactGapCofactorTerm2Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm2Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm2_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 6 = evenCompactGapCofactorTerm2Slice6 u w :=
  (evenCompactGapCofactorTerm2Slice6Certificate u w).eq_value

end
end HTGeometry
