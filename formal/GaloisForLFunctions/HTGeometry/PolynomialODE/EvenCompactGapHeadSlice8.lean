import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorHigherNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Normalized leading-cofactor coefficient at gap degree eight, with its exact certificate. -/
def evenCompactGapHeadSlice8Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapHeadPolynomial u w).coeff 8) :=
  compactGapCofactorHigherCertified% ((evenCompactGapHeadPolynomial u w).coeff 8)

def evenCompactGapHeadSlice8 (u w : ℝ) : ℝ :=
  (evenCompactGapHeadSlice8Certificate u w).value

theorem evenCompactGapHeadPolynomial_coeff_slice8 (u w : ℝ) :
    (evenCompactGapHeadPolynomial u w).coeff 8 = evenCompactGapHeadSlice8 u w :=
  (evenCompactGapHeadSlice8Certificate u w).eq_value

end
end HTGeometry
