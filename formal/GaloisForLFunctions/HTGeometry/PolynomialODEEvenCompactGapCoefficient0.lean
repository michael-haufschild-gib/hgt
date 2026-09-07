import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapDet

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- The constant gap coefficient of the complete corrected determinant is exact. -/
theorem evenCompactGapDetPolynomial_coeff_zero (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 0 = evenCompactRawGapGrade0 u w := by
  rw [Polynomial.coeff_zero_eq_eval_zero, evenCompactGapDetPolynomial_eval]
  norm_num [evenCompactRawDet, hankelFourDet, oddCompactSourceZero,
    oddCompactReflectedScalar2, oddCompactReflectedScalar4, oddCompactReflectedScalar6,
    oddCompactReflectedScalar8, oddCompactReflectedScalar10, evenCompactReflectedScalar12,
    evenCompactRawGapGrade0]
  ring1

end
end HTGeometry
