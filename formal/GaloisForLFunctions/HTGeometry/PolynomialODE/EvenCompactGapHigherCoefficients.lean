import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLowCoefficients

/-! # Fixed-index product formulas for the remaining reversed coefficients -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Exact product coefficient at index 6. -/
theorem evenCompactGapCoeff_mul_6 (p q : Polynomial ℝ) :
    (p*q).coeff 6 =
      p.coeff 0 * q.coeff 6 +
      p.coeff 1 * q.coeff 5 +
      p.coeff 2 * q.coeff 4 +
      p.coeff 3 * q.coeff 3 +
      p.coeff 4 * q.coeff 2 +
      p.coeff 5 * q.coeff 1 +
      p.coeff 6 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 7. -/
theorem evenCompactGapCoeff_mul_7 (p q : Polynomial ℝ) :
    (p*q).coeff 7 =
      p.coeff 0 * q.coeff 7 +
      p.coeff 1 * q.coeff 6 +
      p.coeff 2 * q.coeff 5 +
      p.coeff 3 * q.coeff 4 +
      p.coeff 4 * q.coeff 3 +
      p.coeff 5 * q.coeff 2 +
      p.coeff 6 * q.coeff 1 +
      p.coeff 7 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 8. -/
theorem evenCompactGapCoeff_mul_8 (p q : Polynomial ℝ) :
    (p*q).coeff 8 =
      p.coeff 0 * q.coeff 8 +
      p.coeff 1 * q.coeff 7 +
      p.coeff 2 * q.coeff 6 +
      p.coeff 3 * q.coeff 5 +
      p.coeff 4 * q.coeff 4 +
      p.coeff 5 * q.coeff 3 +
      p.coeff 6 * q.coeff 2 +
      p.coeff 7 * q.coeff 1 +
      p.coeff 8 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 9. -/
theorem evenCompactGapCoeff_mul_9 (p q : Polynomial ℝ) :
    (p*q).coeff 9 =
      p.coeff 0 * q.coeff 9 +
      p.coeff 1 * q.coeff 8 +
      p.coeff 2 * q.coeff 7 +
      p.coeff 3 * q.coeff 6 +
      p.coeff 4 * q.coeff 5 +
      p.coeff 5 * q.coeff 4 +
      p.coeff 6 * q.coeff 3 +
      p.coeff 7 * q.coeff 2 +
      p.coeff 8 * q.coeff 1 +
      p.coeff 9 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 10. -/
theorem evenCompactGapCoeff_mul_10 (p q : Polynomial ℝ) :
    (p*q).coeff 10 =
      p.coeff 0 * q.coeff 10 +
      p.coeff 1 * q.coeff 9 +
      p.coeff 2 * q.coeff 8 +
      p.coeff 3 * q.coeff 7 +
      p.coeff 4 * q.coeff 6 +
      p.coeff 5 * q.coeff 5 +
      p.coeff 6 * q.coeff 4 +
      p.coeff 7 * q.coeff 3 +
      p.coeff 8 * q.coeff 2 +
      p.coeff 9 * q.coeff 1 +
      p.coeff 10 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

end
end HTGeometry
