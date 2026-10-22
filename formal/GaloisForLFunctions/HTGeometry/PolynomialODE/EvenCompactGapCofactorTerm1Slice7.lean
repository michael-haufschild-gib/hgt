import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 1 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm1Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm1 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm1 u w).coeff 7)

def evenCompactGapCofactorTerm1Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 7 = evenCompactGapCofactorTerm1Slice7 u w :=
  (evenCompactGapCofactorTerm1Slice7Certificate u w).eq_value

end
end HTGeometry
