import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree seven, with its exact certificate. -/
def evenCompactGapHeadSlice7Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 7) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 7)

def evenCompactGapHeadSlice7 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice7Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice7 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 7 = evenCompactGapHeadSlice7 u w :=
  (evenCompactGapHeadSlice7Certificate u w).eq_value

end
end HTGeometry
