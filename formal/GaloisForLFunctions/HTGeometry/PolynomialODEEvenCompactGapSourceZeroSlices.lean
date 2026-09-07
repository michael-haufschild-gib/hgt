import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapSourceZeroSlice0 (u : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapSourceZeroCoeff 0 u)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapSourceZeroPolynomial_coeff_slice0 (u : ℝ) :
    (evenCompactGapSourceZeroPolynomial u).coeff 0 = evenCompactGapSourceZeroSlice0 u := by
  rw [evenCompactGapSourceZeroPolynomial_coeff]
  unfold evenCompactGapSourceZeroSlice0
  norm_num [evenCompactGapSourceZeroCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapSourceZeroSlice1 (u : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapSourceZeroCoeff 1 u)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapSourceZeroPolynomial_coeff_slice1 (u : ℝ) :
    (evenCompactGapSourceZeroPolynomial u).coeff 1 = evenCompactGapSourceZeroSlice1 u := by
  rw [evenCompactGapSourceZeroPolynomial_coeff]
  unfold evenCompactGapSourceZeroSlice1
  norm_num [evenCompactGapSourceZeroCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapSourceZeroPolynomial_coeff_above (u : ℝ) (n : ℕ) (hn : 1 < n) :
    (evenCompactGapSourceZeroPolynomial u).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapSourceZeroPolynomial_degree u).trans_lt hn)

end
end HTGeometry
