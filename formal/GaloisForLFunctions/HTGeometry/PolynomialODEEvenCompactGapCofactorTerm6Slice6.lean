import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 6 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm6Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm6 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm6 u w).coeff 6)

def evenCompactGapCofactorTerm6Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm6Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm6_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm6 u w).coeff 6 = evenCompactGapCofactorTerm6Slice6 u w :=
  (evenCompactGapCofactorTerm6Slice6Certificate u w).eq_value

end
end HTGeometry
