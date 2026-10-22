import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 3 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm3Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm3 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm3 u w).coeff 5)

def evenCompactGapCofactorTerm3Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm3Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm3_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm3 u w).coeff 5 = evenCompactGapCofactorTerm3Slice5 u w :=
  (evenCompactGapCofactorTerm3Slice5Certificate u w).eq_value

end
end HTGeometry
