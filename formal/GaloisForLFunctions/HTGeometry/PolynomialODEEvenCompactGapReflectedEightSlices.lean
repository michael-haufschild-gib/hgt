import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedEightSlice0 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 0 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 0 = evenCompactGapReflectedEightSlice0 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice0
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedEightSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 1 = evenCompactGapReflectedEightSlice1 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice1
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedEightSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 2 = evenCompactGapReflectedEightSlice2 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice2
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedEightSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 3 = evenCompactGapReflectedEightSlice3 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice3
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 4. -/
def evenCompactGapReflectedEightSlice4 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 4 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice4 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 4 = evenCompactGapReflectedEightSlice4 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice4
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 5. -/
def evenCompactGapReflectedEightSlice5 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 5 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 5 = evenCompactGapReflectedEightSlice5 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice5
  norm_num [evenCompactGapReflectedEightCoeff]

/-- Normalized source coefficient at gap degree 6. -/
def evenCompactGapReflectedEightSlice6 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedEightCoeff 6 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_slice6 (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff 6 = evenCompactGapReflectedEightSlice6 u w := by
  rw [evenCompactGapReflectedEightPolynomial_coeff]
  unfold evenCompactGapReflectedEightSlice6
  norm_num [evenCompactGapReflectedEightCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedEightPolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 6 < n) :
    (evenCompactGapReflectedEightPolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedEightPolynomial_degree u w).trans_lt hn)

end
end HTGeometry
