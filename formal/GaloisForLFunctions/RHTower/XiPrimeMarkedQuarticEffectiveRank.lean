import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure
import GaloisForLFunctions.RHTower.FiniteThreeLevelMomentCarrier
import GaloisForLFunctions.RHTower.FiniteThreeLevelReverseEndpoint
import Mathlib.Algebra.Order.Chebyshev

/-!
# The K-RVM source needs more than nine head atoms

The existing exact theta bounds place the first two source moments outside
the nine-atom Cauchy cone.  This is a source constraint on the finite head,
independent of any numerical evaluation of zeros.
-/

namespace RHTower

noncomputable section

/-- The source's effective rank is strictly greater than nine. -/
theorem routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy :
    9 * routeKQuarticHalfEnergy < routeKQuarticHalfMass ^ (2 : ℕ) := by
  have hM0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hM1 := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have hM0sq :
      (1 / 25 : ℝ) ^ (2 : ℕ) < normalizedPrimeArchMoment 0 ^ (2 : ℕ) := by
    nlinarith [normalizedPrimeArchMoment_zero_pos]
  have hsource :
      18 * normalizedPrimeArchMoment 1 < normalizedPrimeArchMoment 0 ^ (2 : ℕ) := by
    nlinarith
  rw [routeKQuarticHalfEnergy, routeKQuarticHalfMass,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  nlinarith

/-- The nine-atom Cauchy floor is already too high for the source's quartic
target. -/
theorem routeKNineAtomCauchyFloor_fails :
    ¬ routeKQuarticHalfMass ^ (2 : ℕ) / 9 < routeKQuarticHalfEnergy := by
  nlinarith [routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy]

/-- No real diagonal with nine or fewer coordinates can realize both literal
K-RVM source moments.  Positivity is unnecessary for this obstruction. -/
theorem no_routeKFiniteHead_of_card_le_nine
    {N : ℕ} (hN : N ≤ 9) (x : Fin N → ℝ)
    (hfirst : ∑ i, x i = routeKQuarticHalfMass)
    (hsecond : ∑ i, x i ^ (2 : ℕ) = routeKQuarticHalfEnergy) : False := by
  classical
  have hcs :
      routeKQuarticHalfMass ^ (2 : ℕ) ≤
        (N : ℝ) * routeKQuarticHalfEnergy := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
    simpa [hfirst, hsecond] using h
  have hNreal : (N : ℝ) ≤ 9 := by exact_mod_cast hN
  have hNenergy :
      (N : ℝ) * routeKQuarticHalfEnergy ≤
        9 * routeKQuarticHalfEnergy :=
    mul_le_mul_of_nonneg_right hNreal routeKQuarticHalfEnergy_pos.le
  linarith [routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy]

/-- The actual first two source moments admit a positive equal-share
three-level head, necessarily with at least ten coordinates. -/
theorem exists_routeKThreeLevelFeasibleMeanHead :
    ∃ N : ℕ, 10 ≤ N ∧
      ThreeLevelSpectralFeasible routeKQuarticHalfMass routeKQuarticHalfEnergy
        (routeKQuarticHalfMass / (N : ℝ)) N := by
  have hE := routeKQuarticHalfMass_pos
  have hF := routeKQuarticHalfEnergy_pos
  have hrank := routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy
  obtain ⟨N, hNthree, hfeasible⟩ :=
    exists_threeLevelSpectralFeasible_at_mean hE hF (by nlinarith)
  have hNten : 10 ≤ N := by
    by_contra hnot
    have hNnine : N ≤ 9 := by omega
    have hNreal : (N : ℝ) ≤ 9 := by exact_mod_cast hNnine
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hlow := (threeLevelSpectralFeasible_at_mean_iff hE hNthree).1 hfeasible |>.1
    have hscaled := (div_lt_iff₀ hNpos).1 hlow
    have hupper :=
      mul_le_mul_of_nonneg_right hNreal hF.le
    nlinarith
  exact ⟨N, hNten, hfeasible⟩

/-- The actual source has a positive reverse two-level endpoint with at
least ten atoms.  It matches its quadratic and quartic moments and lies
strictly below the feasible mean endpoint in the cubic coordinate. -/
theorem exists_routeKReverseTwoLevelHead :
    ∃ N : ℕ, 10 ≤ N ∧ ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧
      ((N : ℝ) - 1) * a + b = routeKQuarticHalfMass ∧
      ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) =
        routeKQuarticHalfEnergy ∧
      ThreeLevelSpectralFeasible routeKQuarticHalfMass
        routeKQuarticHalfEnergy a N := by
  have hE := routeKQuarticHalfMass_pos
  have hF := routeKQuarticHalfEnergy_pos
  have hrank := routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy
  obtain ⟨N, hNthree, a, b, hb, hba, hfirst, hsecond, hfeasible⟩ :=
    exists_reverseTwoLevelEndpoint_at_effectiveRank hE hF (by nlinarith)
  have hvar := reverseTwoLevel_variance_identity hfirst hsecond
  have hNten : 10 ≤ N := by
    by_contra hnot
    have hNnine : N ≤ 9 := by omega
    have hNr : (N : ℝ) ≤ 9 := by exact_mod_cast hNnine
    have hNm1 : 0 ≤ (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    have hvariance : 0 ≤
        (N : ℝ) * routeKQuarticHalfEnergy -
          routeKQuarticHalfMass ^ (2 : ℕ) := by
      rw [hvar]
      exact mul_nonneg hNm1 (sq_nonneg (a - b))
    have hupper := mul_le_mul_of_nonneg_right hNr hF.le
    linarith
  exact ⟨N, hNten, a, b, hb, hba, hfirst, hsecond, hfeasible⟩

end

end RHTower
