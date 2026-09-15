import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 1 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm1Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm1 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm1 u w).coeff 5)

def evenCompactGapCofactorTerm1Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm1Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm1_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm1 u w).coeff 5 = evenCompactGapCofactorTerm1Slice5 u w :=
  (evenCompactGapCofactorTerm1Slice5Certificate u w).eq_value

end
end HTGeometry
