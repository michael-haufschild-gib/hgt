import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedSixSlice0 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 0 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 0 = evenCompactGapReflectedSixSlice0 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice0
  norm_num [evenCompactGapReflectedSixCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedSixSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 1 = evenCompactGapReflectedSixSlice1 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice1
  norm_num [evenCompactGapReflectedSixCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedSixSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 2 = evenCompactGapReflectedSixSlice2 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice2
  norm_num [evenCompactGapReflectedSixCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedSixSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 3 = evenCompactGapReflectedSixSlice3 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice3
  norm_num [evenCompactGapReflectedSixCoeff]

/-- Normalized source coefficient at gap degree 4. -/
def evenCompactGapReflectedSixSlice4 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 4 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice4 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 4 = evenCompactGapReflectedSixSlice4 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice4
  norm_num [evenCompactGapReflectedSixCoeff]

/-- Normalized source coefficient at gap degree 5. -/
def evenCompactGapReflectedSixSlice5 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedSixCoeff 5 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff 5 = evenCompactGapReflectedSixSlice5 u w := by
  rw [evenCompactGapReflectedSixPolynomial_coeff]
  unfold evenCompactGapReflectedSixSlice5
  norm_num [evenCompactGapReflectedSixCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedSixPolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 5 < n) :
    (evenCompactGapReflectedSixPolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedSixPolynomial_degree u w).trans_lt hn)

end
end HTGeometry
