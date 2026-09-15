import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 6 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm6Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm6 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm6 u w).coeff 5)

def evenCompactGapCofactorTerm6Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm6Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm6_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm6 u w).coeff 5 = evenCompactGapCofactorTerm6Slice5 u w :=
  (evenCompactGapCofactorTerm6Slice5Certificate u w).eq_value

end
end HTGeometry
