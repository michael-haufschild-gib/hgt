import GaloisForLFunctions.RHTower.CCMPrimeDeficitShortenedCutoff

/-!
# Quantitative variation along the actual Möbius boundary direction

The cubic truncation estimate bounds both the full action change and its
signed second variation. The deformation removes the actual Möbius tail;
no arbitrary-sign cancellation or positivity of the Hessian is assumed.
-/

noncomputable section

namespace RHTower

theorem abs_ccmPrimeDeficitMobiusBoundaryPair_cubic_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) :
    |logarithmicWeightedDilation (logarithmicLongTail m moebiusCoeff)
      (logarithmicWeightedDilation (logarithmicLongTail m moebiusCoeff)
        ccmPrimeDeficitDivisorSource) (2 * Real.log (m + k : ℕ))| ≤
          27 * (k : ℝ) ^ 3 / m := by
  have hT : 0 ≤ 2 * Real.log (m + k : ℕ) := mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)
  rw [← ccmLogChebyshevDeficitPrimitive_sub_truncatedAction m hT]
  exact abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_cubic_le hm hk

theorem abs_ccmPrimeDeficitCoefficientAction_boundary_line_cubic_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (z : ℝ) :
    |ccmPrimeDeficitCoefficientAction (2 * Real.log (m + k : ℕ))
      (fun n => (ArithmeticFunction.moebius n : ℝ) + z * logarithmicLongTail m moebiusCoeff n) -
        ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ))| ≤
          27 * z ^ 2 * (k : ℝ) ^ 3 / m := by
  have hT : 0 ≤ 2 * Real.log (m + k : ℕ) := mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)
  let Q := logarithmicWeightedDilation (logarithmicLongTail m moebiusCoeff)
    (logarithmicWeightedDilation (logarithmicLongTail m moebiusCoeff)
      ccmPrimeDeficitDivisorSource) (2 * Real.log (m + k : ℕ))
  rw [ccmPrimeDeficitCoefficientAction_mobius_line _ hT z]
  change |ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) - z ^ 2 * Q -
    ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ))| ≤ _
  rw [show ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) - z ^ 2 * Q -
    ccmLogChebyshevDeficitPrimitive (2 * Real.log (m + k : ℕ)) = -(z ^ 2 * Q) by ring,
    abs_neg, abs_mul, abs_of_nonneg (sq_nonneg z)]
  calc
    _ ≤ z ^ 2 * (27 * (k : ℝ) ^ 3 / m) :=
      mul_le_mul_of_nonneg_left (abs_ccmPrimeDeficitMobiusBoundaryPair_cubic_le hm hk) (sq_nonneg z)
    _ = _ := by ring

theorem abs_ccmPrimeDeficitCoefficientAction_boundary_second_variation_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (z : ℝ) :
    |deriv (fun q => deriv (fun r => ccmPrimeDeficitCoefficientAction
      (2 * Real.log (m + k : ℕ))
      (fun n => (ArithmeticFunction.moebius n : ℝ) + r * logarithmicLongTail m moebiusCoeff n)) q) z| ≤
        54 * (k : ℝ) ^ 3 / m := by
  rw [(hasDerivAt_deriv_ccmPrimeDeficitCoefficientAction_mobius_line
    (logarithmicLongTail m moebiusCoeff) (2 * Real.log (m + k : ℕ)) z).deriv,
    abs_mul]
  rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
  calc
    _ ≤ 2 * (27 * (k : ℝ) ^ 3 / m) :=
      mul_le_mul_of_nonneg_left (abs_ccmPrimeDeficitMobiusBoundaryPair_cubic_le hm hk) (by norm_num)
    _ = _ := by ring

end RHTower
