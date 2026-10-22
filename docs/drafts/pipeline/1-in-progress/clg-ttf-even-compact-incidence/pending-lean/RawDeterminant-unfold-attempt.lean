import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactRawModel

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000
open GaloisForLFunctions.HTGeometry

/-- Exact original-coordinate determinant identity before the coupled gap is substituted. -/
theorem evenCompactRawDet_eq_polynomial (u a w : ℝ) :
    evenCompactRawDet u a w = evenCompactRawPolynomial u a w := by
  unfold evenCompactRawDet hankelFourDet oddCompactSourceZero
    oddCompactReflectedScalar2 oddCompactReflectedScalar4 oddCompactReflectedScalar6
    oddCompactReflectedScalar8 oddCompactReflectedScalar10 evenCompactReflectedScalar12
    evenCompactRawPolynomial evenCompactRawGapGrade0 evenCompactRawGapGrade1 evenCompactRawGapGrade2 evenCompactRawGapGrade3 evenCompactRawGapGrade4 evenCompactRawGapGrade5 evenCompactRawGapGrade6 evenCompactRawGapGrade7 evenCompactRawGapGrade8 evenCompactRawGapGrade9 evenCompactRawGapGrade10 evenCompactRawGapGrade11 evenCompactRawGapGrade12 evenCompactRawGapGrade13 evenCompactRawGapGrade14 evenCompactRawGapGrade15 evenCompactRawGapGrade16 evenCompactRawGapGrade17 evenCompactRawGapGrade18 evenCompactRawGapGrade19 evenCompactRawGapGrade20
  ring1

end
end HTGeometry
