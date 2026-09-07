import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedTwelveSlice0 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 0 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 0 = evenCompactGapReflectedTwelveSlice0 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice0
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedTwelveSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 1 = evenCompactGapReflectedTwelveSlice1 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice1
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedTwelveSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 2 = evenCompactGapReflectedTwelveSlice2 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice2
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedTwelveSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 3 = evenCompactGapReflectedTwelveSlice3 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice3
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 4. -/
def evenCompactGapReflectedTwelveSlice4 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 4 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice4 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 4 = evenCompactGapReflectedTwelveSlice4 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice4
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 5. -/
def evenCompactGapReflectedTwelveSlice5 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 5 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 5 = evenCompactGapReflectedTwelveSlice5 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice5
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 6. -/
def evenCompactGapReflectedTwelveSlice6 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 6 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice6 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 6 = evenCompactGapReflectedTwelveSlice6 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice6
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 7. -/
def evenCompactGapReflectedTwelveSlice7 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 7 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice7 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 7 = evenCompactGapReflectedTwelveSlice7 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice7
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- Normalized source coefficient at gap degree 8. -/
def evenCompactGapReflectedTwelveSlice8 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTwelveCoeff 8 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_slice8 (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff 8 = evenCompactGapReflectedTwelveSlice8 u w := by
  rw [evenCompactGapReflectedTwelvePolynomial_coeff]
  unfold evenCompactGapReflectedTwelveSlice8
  norm_num [evenCompactGapReflectedTwelveCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 8 < n) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedTwelvePolynomial_degree u w).trans_lt hn)

end
end HTGeometry
