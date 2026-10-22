import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 2 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm2Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm2 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm2 u w).coeff 7)

def evenCompactGapCofactorTerm2Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm2Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm2_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm2 u w).coeff 7 = evenCompactGapCofactorTerm2Slice7 u w :=
  (evenCompactGapCofactorTerm2Slice7Certificate u w).eq_value

end
end HTGeometry
