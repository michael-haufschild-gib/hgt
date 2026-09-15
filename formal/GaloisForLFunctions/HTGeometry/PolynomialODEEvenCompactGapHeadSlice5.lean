import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree five, with its exact certificate. -/
def evenCompactGapHeadSlice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 5) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 5)

def evenCompactGapHeadSlice5 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice5Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 5 = evenCompactGapHeadSlice5 u w :=
  (evenCompactGapHeadSlice5Certificate u w).eq_value

end
end HTGeometry
