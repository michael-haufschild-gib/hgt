import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapConvolution

/-! # Finite coefficient product formulas without symbolic summation indices -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- Exact product coefficient at index 2. -/
theorem evenCompactGapCoeff_mul_2 (p q : Polynomial ℝ) :
    (p*q).coeff 2 =
      p.coeff 0 * q.coeff 2 +
      p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 3. -/
theorem evenCompactGapCoeff_mul_3 (p q : Polynomial ℝ) :
    (p*q).coeff 3 =
      p.coeff 0 * q.coeff 3 +
      p.coeff 1 * q.coeff 2 +
      p.coeff 2 * q.coeff 1 +
      p.coeff 3 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 4. -/
theorem evenCompactGapCoeff_mul_4 (p q : Polynomial ℝ) :
    (p*q).coeff 4 =
      p.coeff 0 * q.coeff 4 +
      p.coeff 1 * q.coeff 3 +
      p.coeff 2 * q.coeff 2 +
      p.coeff 3 * q.coeff 1 +
      p.coeff 4 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

/-- Exact product coefficient at index 5. -/
theorem evenCompactGapCoeff_mul_5 (p q : Polynomial ℝ) :
    (p*q).coeff 5 =
      p.coeff 0 * q.coeff 5 +
      p.coeff 1 * q.coeff 4 +
      p.coeff 2 * q.coeff 3 +
      p.coeff 3 * q.coeff 2 +
      p.coeff 4 * q.coeff 1 +
      p.coeff 5 * q.coeff 0 := by
  norm_num [evenCompactGapCoeff_mul, Finset.sum_range_succ]

end
end HTGeometry
