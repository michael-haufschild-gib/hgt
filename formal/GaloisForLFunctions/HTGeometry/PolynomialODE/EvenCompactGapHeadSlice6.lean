import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree six, with its exact certificate. -/
def evenCompactGapHeadSlice6Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 6) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 6)

def evenCompactGapHeadSlice6 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice6Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice6 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 6 = evenCompactGapHeadSlice6 u w :=
  (evenCompactGapHeadSlice6Certificate u w).eq_value

end
end HTGeometry
