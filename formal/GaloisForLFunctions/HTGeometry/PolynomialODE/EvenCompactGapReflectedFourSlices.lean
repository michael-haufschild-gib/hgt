import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapSliceNormalizer

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Normalized source coefficient at gap degree 0. -/
def evenCompactGapReflectedFourSlice0 (u _w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedFourCoeff 0 u _w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_slice0 (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff 0 = evenCompactGapReflectedFourSlice0 u w := by
  rw [evenCompactGapReflectedFourPolynomial_coeff]
  unfold evenCompactGapReflectedFourSlice0
  norm_num [evenCompactGapReflectedFourCoeff]

/-- Normalized source coefficient at gap degree 1. -/
def evenCompactGapReflectedFourSlice1 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedFourCoeff 1 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_slice1 (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff 1 = evenCompactGapReflectedFourSlice1 u w := by
  rw [evenCompactGapReflectedFourPolynomial_coeff]
  unfold evenCompactGapReflectedFourSlice1
  norm_num [evenCompactGapReflectedFourCoeff]

/-- Normalized source coefficient at gap degree 2. -/
def evenCompactGapReflectedFourSlice2 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedFourCoeff 2 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_slice2 (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff 2 = evenCompactGapReflectedFourSlice2 u w := by
  rw [evenCompactGapReflectedFourPolynomial_coeff]
  unfold evenCompactGapReflectedFourSlice2
  norm_num [evenCompactGapReflectedFourCoeff]

/-- Normalized source coefficient at gap degree 3. -/
def evenCompactGapReflectedFourSlice3 (u w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedFourCoeff 3 u w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_slice3 (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff 3 = evenCompactGapReflectedFourSlice3 u w := by
  rw [evenCompactGapReflectedFourPolynomial_coeff]
  unfold evenCompactGapReflectedFourSlice3
  norm_num [evenCompactGapReflectedFourCoeff]

/-- Normalized source coefficient at gap degree 4. -/
def evenCompactGapReflectedFourSlice4 (_u _w : ℝ) : ℝ :=
  compactGapSlice% (evenCompactGapReflectedFourCoeff 4 _u _w)

/-- Exact source extraction, independently checked against the original polynomial. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_slice4 (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff 4 = evenCompactGapReflectedFourSlice4 u w := by
  rw [evenCompactGapReflectedFourPolynomial_coeff]
  unfold evenCompactGapReflectedFourSlice4
  norm_num [evenCompactGapReflectedFourCoeff]

/-- The proved source degree bound annihilates every higher coefficient. -/
theorem evenCompactGapReflectedFourPolynomial_coeff_above (u w : ℝ) (n : ℕ) (hn : 4 < n) :
    (evenCompactGapReflectedFourPolynomial u w).coeff n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((evenCompactGapReflectedFourPolynomial_degree u w).trans_lt hn)

end
end HTGeometry
