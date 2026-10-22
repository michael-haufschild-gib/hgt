import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree 10, with its exact certificate. -/
def evenCompactGapHeadSlice10Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 10) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 10)

def evenCompactGapHeadSlice10 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice10Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice10 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 10 = evenCompactGapHeadSlice10 u w :=
  (evenCompactGapHeadSlice10Certificate u w).eq_value

end
end HTGeometry
