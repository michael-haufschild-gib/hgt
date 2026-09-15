import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 4 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm4Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm4 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm4 u w).coeff 7)

def evenCompactGapCofactorTerm4Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm4Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm4_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm4 u w).coeff 7 = evenCompactGapCofactorTerm4Slice7 u w :=
  (evenCompactGapCofactorTerm4Slice7Certificate u w).eq_value

end
end HTGeometry
