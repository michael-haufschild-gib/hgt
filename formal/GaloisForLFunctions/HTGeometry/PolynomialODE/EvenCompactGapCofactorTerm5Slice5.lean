import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 5 coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapCofactorTerm5Slice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm5 u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm5 u w).coeff 5)

def evenCompactGapCofactorTerm5Slice5 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm5Slice5Certificate u w).value

theorem evenCompactGapCofactorTerm5_coeff_slice5 (u w : ℝ) :
    (evenCompactGapCofactorTerm5 u w).coeff 5 = evenCompactGapCofactorTerm5Slice5 u w :=
  (evenCompactGapCofactorTerm5Slice5Certificate u w).eq_value

end
end HTGeometry
