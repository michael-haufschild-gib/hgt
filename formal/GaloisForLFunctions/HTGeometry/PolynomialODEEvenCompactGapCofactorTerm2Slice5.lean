import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 2 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm2Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm2 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm2 u w).coeff 5)

def evenCompactGapCofactorTerm2Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm2Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm2_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 5 = evenCompactGapCofactorTerm2Slice5 u w :=
  (evenCompactGapCofactorTerm2Slice5Certificate u w).eq_value

end
end HTGeometry
