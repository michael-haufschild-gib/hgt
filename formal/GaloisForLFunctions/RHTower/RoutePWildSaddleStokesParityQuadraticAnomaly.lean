import GaloisForLFunctions.RHTower.RoutePWildSaddleMinimalTraceClassDepth

/-!
# Route P wild-saddle Stokes-parity quadratic anomaly

Opposite Stokes orientations cancel the primewise linear coordinate of a signed correction, but
they do not cancel its Hilbert--Carleman determinant data.  This file compares the source-only
first and second logarithmic stationary-phase saddles.  At every prime the second reciprocal is
strictly larger, and the resulting square difference is positive and summable.

Thus the one-to-two-step correction is formally invisible to primewise signed first-coordinate
pairing but visible in the quadratic `det₂` coordinate.  No global first trace of that correction
is asserted.  Trace-class relocation cannot be promoted to determinant equality by parity alone.
No Xi ordinate or RH assumption enters the result.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

/-- The second logarithmic fixed-point iterate strictly improves the first at every source mass. -/
theorem routePTwoStepWildSaddleFirstPhase_lt_secondPhase (n : ℕ) :
    routePTwoStepWildSaddleFirstPhase n <
      routePTwoStepWildSaddleSecondPhase n := by
  have hL : 2 ≤ routePTwoStepWildSaddleLogPhase n :=
    routePTwoStepWildSaddleLogPhase_ge_two n
  have hLpos : 0 < routePTwoStepWildSaddleLogPhase n := by linarith
  have hfirstPos : 0 < routePTwoStepWildSaddleFirstPhase n :=
    zero_lt_one.trans_le (routePTwoStepWildSaddleFirstPhase_one_le n)
  have hlogLpos : 0 < Real.log (routePTwoStepWildSaddleLogPhase n) :=
    Real.log_pos (by linarith)
  have hfirstLt : routePTwoStepWildSaddleFirstPhase n <
      routePTwoStepWildSaddleLogPhase n := by
    rw [routePTwoStepWildSaddleFirstPhase]
    linarith
  have hlogLt : Real.log (routePTwoStepWildSaddleFirstPhase n) <
      Real.log (routePTwoStepWildSaddleLogPhase n) :=
    Real.strictMonoOn_log hfirstPos hLpos hfirstLt
  rw [routePTwoStepWildSaddleSecondPhase]
  have hgap : routePTwoStepWildSaddleLogPhase n -
      routePTwoStepWildSaddleFirstPhase n =
        Real.log (routePTwoStepWildSaddleLogPhase n) := by
    rw [routePTwoStepWildSaddleFirstPhase]
    ring
  linarith

/-- Prime-labelled form of strict improvement by the second wild-saddle correction. -/
theorem routePOneStepWildSaddlePrimeReciprocal_lt_twoStep (p : Nat.Primes) :
    routePOneStepWildSaddlePrimeReciprocal p <
      routePTwoStepWildSaddlePrimeReciprocal p := by
  rw [routePOneStepWildSaddlePrimeReciprocal,
    routePTwoStepWildSaddlePrimeReciprocal,
    routePOneStepWildSaddleReciprocal,
    routePTwoStepWildSaddleReciprocal]
  exact div_lt_div_of_pos_right
    (routePTwoStepWildSaddleFirstPhase_lt_secondPhase _)
    (mul_pos (by positivity) (routePTwoStepWildSaddleMass_pos _))

/-- First even Hilbert--Carleman coordinate changed by the second stationary-phase correction. -/
def routePWildSaddleQuadraticDet2Anomaly (p : Nat.Primes) : ℝ :=
  routePTwoStepWildSaddlePrimeReciprocal p ^ 2 -
    routePOneStepWildSaddlePrimeReciprocal p ^ 2

theorem routePWildSaddleQuadraticDet2Anomaly_pos (p : Nat.Primes) :
    0 < routePWildSaddleQuadraticDet2Anomaly p := by
  rw [routePWildSaddleQuadraticDet2Anomaly]
  nlinarith [routePOneStepWildSaddlePrimeReciprocal_lt_twoStep p,
    routePOneStepWildSaddlePrimeReciprocal_nonneg p,
    routePTwoStepWildSaddlePrimeReciprocal_nonneg p]

/-- The surviving quadratic anomaly is trace class even though the one-step linear relocation
defect is not. -/
theorem summable_routePWildSaddleQuadraticDet2Anomaly :
    Summable routePWildSaddleQuadraticDet2Anomaly := by
  have htwoHS : routePTwoStepWildSaddleSignedOperator.IsHilbertSchmidt :=
    (memSchattenClass_two_iff_isHilbertSchmidt _).mp
      routePTwoStepWildSaddleSignedOperator_memSchattenClass_two
  have hsumSigned : Summable (fun i : RouteKSignedPrimeIndex =>
      ‖routePTwoStepWildSaddleSignedMultiplier i‖ ^ 2) :=
    (HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff
      routePTwoStepWildSaddleSignedMultiplier
      norm_routePTwoStepWildSaddleSignedMultiplier_le_one).mp htwoHS
  have hsumPosNorm : Summable (fun p : Nat.Primes =>
      ‖(routePTwoStepWildSaddlePrimeReciprocal p : ℂ)‖ ^ 2) := by
    simpa [Function.comp_def, routePTwoStepWildSaddleSignedMultiplier,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (routePTwoStepWildSaddlePrimeReciprocal_nonneg _)] using
      hsumSigned.comp_injective Sum.inl_injective
  have hsumPos : Summable (fun p : Nat.Primes =>
      routePTwoStepWildSaddlePrimeReciprocal p ^ 2) := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (routePTwoStepWildSaddlePrimeReciprocal_nonneg _)] using
      hsumPosNorm
  refine Summable.of_nonneg_of_le
    (fun p => (routePWildSaddleQuadraticDet2Anomaly_pos p).le) ?_ hsumPos
  intro p
  rw [routePWildSaddleQuadraticDet2Anomaly]
  nlinarith [sq_nonneg (routePOneStepWildSaddlePrimeReciprocal p)]

/-- Total source-only quadratic determinant anomaly. -/
def routePWildSaddleTotalQuadraticDet2Anomaly : ℝ :=
  ∑' p : Nat.Primes, routePWildSaddleQuadraticDet2Anomaly p

theorem routePWildSaddleTotalQuadraticDet2Anomaly_pos :
    0 < routePWildSaddleTotalQuadraticDet2Anomaly := by
  rw [routePWildSaddleTotalQuadraticDet2Anomaly]
  exact summable_routePWildSaddleQuadraticDet2Anomaly.tsum_pos
    (fun p => (routePWildSaddleQuadraticDet2Anomaly_pos p).le)
    ⟨2, Nat.prime_two⟩
    (routePWildSaddleQuadraticDet2Anomaly_pos ⟨2, Nat.prime_two⟩)

/-- Signed one-to-two-step Stokes correction. -/
def routePWildSaddleOneToTwoCorrectionMultiplier : RouteKSignedPrimeIndex → ℝ
  | Sum.inl p => routePTwoStepWildSaddlePrimeReciprocal p -
      routePOneStepWildSaddlePrimeReciprocal p
  | Sum.inr p => -(routePTwoStepWildSaddlePrimeReciprocal p -
      routePOneStepWildSaddlePrimeReciprocal p)

/-- Opposite orientations cancel the linear correction prime by prime.  This is not a claim that
the full one-to-two-step correction is trace class. -/
theorem routePWildSaddleOneToTwoCorrectionMultiplier_pair_sum_zero (p : Nat.Primes) :
    routePWildSaddleOneToTwoCorrectionMultiplier (Sum.inl p) +
      routePWildSaddleOneToTwoCorrectionMultiplier (Sum.inr p) = 0 := by
  simp [routePWildSaddleOneToTwoCorrectionMultiplier]

/-- The same signed pair doubles, rather than cancels, its quadratic correction. -/
theorem routePWildSaddle_pairQuadraticCorrection_eq (p : Nat.Primes) :
    routePTwoStepWildSaddlePrimeReciprocal p ^ 2 +
        (-routePTwoStepWildSaddlePrimeReciprocal p) ^ 2 -
      (routePOneStepWildSaddlePrimeReciprocal p ^ 2 +
        (-routePOneStepWildSaddlePrimeReciprocal p) ^ 2) =
      2 * routePWildSaddleQuadraticDet2Anomaly p := by
  rw [routePWildSaddleQuadraticDet2Anomaly]
  ring

theorem routePWildSaddle_pairQuadraticCorrection_pos (p : Nat.Primes) :
    0 < routePTwoStepWildSaddlePrimeReciprocal p ^ 2 +
        (-routePTwoStepWildSaddlePrimeReciprocal p) ^ 2 -
      (routePOneStepWildSaddlePrimeReciprocal p ^ 2 +
        (-routePOneStepWildSaddlePrimeReciprocal p) ^ 2) := by
  rw [routePWildSaddle_pairQuadraticCorrection_eq]
  nlinarith [routePWildSaddleQuadraticDet2Anomaly_pos p]

/-- Scalar determinant mechanism: exponential counterterms cancel across a signed pair, leaving
the square-spectrum factor. -/
theorem pairedDet2Factor_eq_squareFactor (a z : ℂ) :
    ((1 - z * a) * Complex.exp (z * a)) *
        ((1 + z * a) * Complex.exp (-(z * a))) =
      1 - z ^ 2 * a ^ 2 := by
  calc
    ((1 - z * a) * Complex.exp (z * a)) *
          ((1 + z * a) * Complex.exp (-(z * a))) =
        ((1 - z * a) * (1 + z * a)) *
          (Complex.exp (z * a) * Complex.exp (-(z * a))) := by ring
    _ = (1 - z * a) * (1 + z * a) := by
      rw [← Complex.exp_add]
      simp
    _ = 1 - z ^ 2 * a ^ 2 := by ring

/-- At determinant parameter one, every second-step square factor is strictly below the
corresponding first-step factor. -/
theorem routePWildSaddle_twoStep_squareFactor_lt_oneStep (p : Nat.Primes) :
    1 - routePTwoStepWildSaddlePrimeReciprocal p ^ 2 <
      1 - routePOneStepWildSaddlePrimeReciprocal p ^ 2 := by
  have h := routePWildSaddleQuadraticDet2Anomaly_pos p
  rw [routePWildSaddleQuadraticDet2Anomaly] at h
  linarith

/-- Source-only no-go and positive survivor: primewise signed linear coordinates cancel, while a
positive summable quadratic determinant anomaly remains. -/
theorem routeP_wildSaddle_stokesParity_quadraticAnomaly :
    (∀ p : Nat.Primes,
      routePWildSaddleOneToTwoCorrectionMultiplier (Sum.inl p) +
        routePWildSaddleOneToTwoCorrectionMultiplier (Sum.inr p) = 0) ∧
    Summable routePWildSaddleQuadraticDet2Anomaly ∧
    0 < routePWildSaddleTotalQuadraticDet2Anomaly ∧
    ∀ p : Nat.Primes,
      1 - routePTwoStepWildSaddlePrimeReciprocal p ^ 2 <
        1 - routePOneStepWildSaddlePrimeReciprocal p ^ 2 := by
  exact ⟨routePWildSaddleOneToTwoCorrectionMultiplier_pair_sum_zero,
    summable_routePWildSaddleQuadraticDet2Anomaly,
    routePWildSaddleTotalQuadraticDet2Anomaly_pos,
    routePWildSaddle_twoStep_squareFactor_lt_oneStep⟩

end

end RHTower
