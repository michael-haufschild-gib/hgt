import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 6 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm6Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm6 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm6 u w).coeff 7)

def evenCompactGapCofactorTerm6Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm6Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm6_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm6 u w).coeff 7 = evenCompactGapCofactorTerm6Slice7 u w :=
  (evenCompactGapCofactorTerm6Slice7Certificate u w).eq_value

end
end HTGeometry
