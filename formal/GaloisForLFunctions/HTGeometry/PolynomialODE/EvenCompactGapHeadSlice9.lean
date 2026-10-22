import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree 9, with its exact certificate. -/
def evenCompactGapHeadSlice9Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 9) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 9)

def evenCompactGapHeadSlice9 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice9Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice9 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 9 = evenCompactGapHeadSlice9 u w :=
  (evenCompactGapHeadSlice9Certificate u w).eq_value

end
end HTGeometry
