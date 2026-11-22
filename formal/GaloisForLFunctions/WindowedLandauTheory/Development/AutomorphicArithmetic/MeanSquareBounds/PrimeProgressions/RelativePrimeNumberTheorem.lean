import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevFarRange
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevGlue
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevNearRange
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevSharpen
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimeCountOfChebyshev

/-! The relative prime number theorem for the moving progressions of auxiliary primes. -/

namespace QH.PrimeProgressions

theorem psi_relative_polynomial_holds : PsiRelPolynomial :=
  glue_polynomial_ranges
    (psi_relative_near_range truncated_normalized_explicit_formula differenced_explicit_formula)
    (psi_relative_far_range_polynomial differenced_explicit_formula)

theorem pnt_progressions_relative_holds : PNTAPRelPolynomial :=
  prime_count_of_psi psi_relative_polynomial_holds

theorem pnt_progressions_relative_weak_holds : PNTAPRelW := by
  obtain ⟨c, A, C, hc, hP⟩ := pnt_progressions_relative_holds
  refine ⟨c, A, max C 0, hc, fun M _ h8 => ?_⟩
  obtain ⟨e, hE, hNo, h⟩ := hP M h8
  refine ⟨e, hE, hNo, fun X b hX hL hb => h X b hX ?_ hb⟩
  have hM : 8 ≤ M := Nat.le_of_dvd (NeZero.pos M) h8
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hl := one_le_log_of_three_le (by linarith only [hMr] : (3 : ℝ) ≤ M)
  have hll := one_le_log_of_three_le (by linarith only [hl] : (3 : ℝ) ≤ Real.log M + 2)
  calc C * Real.log M ≤ max C 0 * Real.log M :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [hl])
    _ ≤ _ := (le_mul_of_one_le_right (by positivity) hll).trans hL

end QH.PrimeProgressions
