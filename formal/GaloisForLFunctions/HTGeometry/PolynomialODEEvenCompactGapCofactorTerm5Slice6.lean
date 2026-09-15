import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized adjugate contribution 5 coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapCofactorTerm5Slice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapCofactorTerm5 u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapCofactorTerm5 u w).coeff 6)

def evenCompactGapCofactorTerm5Slice6 (u w : ℝ) : ℝ :=
  (evenCompactGapCofactorTerm5Slice6Certificate u w).value

theorem evenCompactGapCofactorTerm5_coeff_slice6 (u w : ℝ) :
    (evenCompactGapCofactorTerm5 u w).coeff 6 = evenCompactGapCofactorTerm5Slice6 u w :=
  (evenCompactGapCofactorTerm5Slice6Certificate u w).eq_value

end
end HTGeometry
