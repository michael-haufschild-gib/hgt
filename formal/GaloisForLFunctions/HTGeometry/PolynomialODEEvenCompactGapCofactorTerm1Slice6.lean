import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 1 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm1Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm1 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm1 u w).coeff 6)

def evenCompactGapCofactorTerm1Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 6 = evenCompactGapCofactorTerm1Slice6 u w :=
  (evenCompactGapCofactorTerm1Slice6Certificate u w).eq_value

end
end HTGeometry
