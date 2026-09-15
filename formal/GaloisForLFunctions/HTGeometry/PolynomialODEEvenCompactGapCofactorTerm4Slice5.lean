import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 4 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm4Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm4 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm4 u w).coeff 5)

def evenCompactGapCofactorTerm4Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm4Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm4_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm4 u w).coeff 5 = evenCompactGapCofactorTerm4Slice5 u w :=
  (evenCompactGapCofactorTerm4Slice5Certificate u w).eq_value

end
end HTGeometry
