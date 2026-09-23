import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature

/-!
# Multiplicative coordinates for the rectangular screw curvature

When the fixed width is `log m` and the screw coordinate is
`log (m^(2 : ℕ) n)`, the three moving samples are exactly the multiplicative
triple `n, mn, m^(2 : ℕ) n`.  This exposes the rectangular RH detector as a
multiplicative midpoint curvature, the form needed by any arithmetic
covariance or conditional-negative-type construction.
-/

open Complex

namespace RHTower

noncomputable section

/-- The fixed-width screw curvature on a multiplicative integer triple. -/
theorem xiScrewWindowCurvature_log_mul_sq
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    xiScrewWindowCurvature (Real.log m)
        (Real.log ((m ^ 2 * n : ℕ) : ℝ)) =
      2 * (xiScrewDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) +
        xiScrewDivisor (Real.log n) -
        2 * xiScrewDivisor (Real.log ((m * n : ℕ) : ℝ)) +
        2 * xiScrewDivisor (Real.log m)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hmn0 : ((m : ℝ) * n) ≠ 0 := mul_ne_zero hm0 hn0
  have hlogmn : Real.log ((m * n : ℕ) : ℝ) =
      Real.log m + Real.log n := by
    push_cast
    exact Real.log_mul hm0 hn0
  have hlogm2n :
      Real.log ((m ^ 2 * n : ℕ) : ℝ) =
        2 * Real.log m + Real.log n := by
    push_cast
    rw [show (m : ℝ) ^ 2 * n = (m : ℝ) * ((m : ℝ) * n) by ring,
      Real.log_mul hm0 hmn0, Real.log_mul hm0 hn0]
    ring
  rw [xiScrewWindowCurvature, hlogm2n, hlogmn]
  ring_nf

/-- The logarithmically sampled rectangular Weil value at `m^(2 : ℕ) n` is the
multiplicative midpoint curvature of the Xi screw profile. -/
theorem xiWeilPolarization_rectangular_log_mul_sq_eq_screwCurvature
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    xiWeilPolarization
        (xiRectangularTwoEdgeTransform (Real.log m)
          (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2))
        (xiRectangularTwoEdgeTransform (Real.log m)
          (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2)) =
      2 * (xiScrewDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) +
        xiScrewDivisor (Real.log n) -
        2 * xiScrewDivisor (Real.log ((m * n : ℕ) : ℝ)) +
        2 * xiScrewDivisor (Real.log m)) := by
  rw [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
  exact xiScrewWindowCurvature_log_mul_sq hm hn

end

end RHTower
