import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 5 coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapCofactorTerm5Slice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm5 u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm5 u w).coeff 7)

def evenCompactGapCofactorTerm5Slice7 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm5Slice7Certificate u w).value

theorem evenCompactGapCofactorTerm5_coeff_slice7 (u w : ℝ) :
    (evenCompactGapCofactorTerm5 u w).coeff 7 = evenCompactGapCofactorTerm5Slice7 u w :=
  (evenCompactGapCofactorTerm5Slice7Certificate u w).eq_value

end
end HTGeometry
