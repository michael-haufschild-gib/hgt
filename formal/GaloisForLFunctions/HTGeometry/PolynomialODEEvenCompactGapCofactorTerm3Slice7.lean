import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 3 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm3Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm3 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm3 u w).coeff 7)

def evenCompactGapCofactorTerm3Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm3Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm3_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm3 u w).coeff 7 = evenCompactGapCofactorTerm3Slice7 u w :=
  (evenCompactGapCofactorTerm3Slice7Certificate u w).eq_value

end
end HTGeometry
