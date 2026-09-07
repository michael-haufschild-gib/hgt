import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedTenSlice0 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 0 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 0 = evenCompactGapReflectedTenSlice0 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice0
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedTenSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 1 = evenCompactGapReflectedTenSlice1 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice1
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedTenSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 2 = evenCompactGapReflectedTenSlice2 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice2
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedTenSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 3 = evenCompactGapReflectedTenSlice3 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice3
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 4. -/
def evenCompactGapReflectedTenSlice4 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 4 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice4 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 4 = evenCompactGapReflectedTenSlice4 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice4
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 5. -/
def evenCompactGapReflectedTenSlice5 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 5 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 5 = evenCompactGapReflectedTenSlice5 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice5
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 6. -/
def evenCompactGapReflectedTenSlice6 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 6 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice6 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 6 = evenCompactGapReflectedTenSlice6 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice6
  norm_num [evenCompactGapReflectedTenCoeff]

/-- Normalized source coefficient at gap degree 7. -/
def evenCompactGapReflectedTenSlice7 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedTenCoeff 7 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_slice7 (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff 7 = evenCompactGapReflectedTenSlice7 u w := by
  rw [evenCompactGapReflectedTenPolynomial_coeff]
  unfold evenCompactGapReflectedTenSlice7
  norm_num [evenCompactGapReflectedTenCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedTenPolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 7 < n) :
    (evenCompactGapReflectedTenPolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedTenPolynomial_degree u w).trans_lt hn)

end
end HTGeometry
