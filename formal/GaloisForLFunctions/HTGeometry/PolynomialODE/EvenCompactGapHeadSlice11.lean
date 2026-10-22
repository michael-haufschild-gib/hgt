import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTopNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree 11, with its exact certificate. -/
def evenCompactGapHeadSlice11Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapHeadPolynomial u w).coeff 11)

def evenCompactGapHeadSlice11 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice11Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice11 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 11 = evenCompactGapHeadSlice11 u w :=
  (evenCompactGapHeadSlice11Certificate u w).eq_value

end
end HTGeometry
