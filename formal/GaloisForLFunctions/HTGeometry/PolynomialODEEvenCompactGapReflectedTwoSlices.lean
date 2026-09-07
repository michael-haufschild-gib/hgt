import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedTwoSlice0 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwoCoeff 0 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff 0 = evenCompactGapReflectedTwoSlice0 u w := by
  rw [evenCompactGapReflectedTwoPolynomial_coeff]
  unfold evenCompactGapReflectedTwoSlice0
  norm_num [evenCompactGapReflectedTwoCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedTwoSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwoCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff 1 = evenCompactGapReflectedTwoSlice1 u w := by
  rw [evenCompactGapReflectedTwoPolynomial_coeff]
  unfold evenCompactGapReflectedTwoSlice1
  norm_num [evenCompactGapReflectedTwoCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedTwoSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwoCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff 2 = evenCompactGapReflectedTwoSlice2 u w := by
  rw [evenCompactGapReflectedTwoPolynomial_coeff]
  unfold evenCompactGapReflectedTwoSlice2
  norm_num [evenCompactGapReflectedTwoCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedTwoSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwoCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff 3 = evenCompactGapReflectedTwoSlice3 u w := by
  rw [evenCompactGapReflectedTwoPolynomial_coeff]
  unfold evenCompactGapReflectedTwoSlice3
  norm_num [evenCompactGapReflectedTwoCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 3 < n) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedTwoPolynomial_degree u w).trans_lt hn)

end
end HTGeometry
