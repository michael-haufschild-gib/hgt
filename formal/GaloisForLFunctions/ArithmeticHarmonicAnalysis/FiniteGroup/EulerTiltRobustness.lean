import GaloisForLFunctions.RHTower.RouteEMovingEulerTiltChiSquareContiguity

/-!
# Variance-sensitive robustness of finite Euler tilts

Centering the observable sharpens the finite Euler-tilt transfer bound from
its second moment to its variance. The resulting certificate depends only
on fluctuations and survives every additive shift of the observable.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open _root_.RHTower _root_.HTGeometry.ConstraintFrameRelativity
noncomputable section

/-- Centered variance of an observable under the finite Euler occupation law. -/
def eulerTiltVariance (σ : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) : ℝ :=
  routeEEulerBernoulliExpBelow σ N
    (fun S => (f S - routeEEulerBernoulliExpBelow σ N f) ^ (2 : ℕ))

/-- The centered Euler variance is nonnegative at every real tilt. -/
theorem eulerTiltVariance_nonneg (σ : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) : 0 ≤ eulerTiltVariance σ N f := by
  exact bernoulliExp_sq_nonneg _
    (fun p => (routeEEulerBernoulliProb_pos σ p.1).le)
    (fun p => (routeEEulerBernoulliProb_lt_one σ p.1).le) _

/-- Finite Euler expectation preserves subtraction of constants. -/
theorem eulerTiltExpectation_sub_const (σ : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) (c : ℝ) :
    routeEEulerBernoulliExpBelow σ N (fun S => f S - c) =
      routeEEulerBernoulliExpBelow σ N f - c := by
  have hmass : (∑ S : Finset ↥(Sieve.primeSubtypeLE N),
      bernoulliWeight (fun p => routeEEulerBernoulliProb σ p.1) S) = 1 := by
    simpa only [bernoulliExp, mul_one] using
      bernoulliExp_one (fun p : ↥(Sieve.primeSubtypeLE N) => routeEEulerBernoulliProb σ p.1)
  simp only [routeEEulerBernoulliExpBelow, bernoulliExp, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]

/-- Centered variance equals the existing Boolean covariance form. -/
theorem eulerTiltVariance_eq_covariance (σ : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) :
    eulerTiltVariance σ N f =
      bernoulliCov (fun p : ↥(Sieve.primeSubtypeLE N) => routeEEulerBernoulliProb σ p.1) f f := by
  have hmass : (∑ S : Finset ↥(Sieve.primeSubtypeLE N),
      bernoulliWeight (fun p => routeEEulerBernoulliProb σ p.1) S) = 1 := by
    simpa only [bernoulliExp, mul_one] using
      bernoulliExp_one (fun p : ↥(Sieve.primeSubtypeLE N) => routeEEulerBernoulliProb σ p.1)
  unfold eulerTiltVariance bernoulliCov routeEEulerBernoulliExpBelow bernoulliExp
  simp_rw [show ∀ w x m : ℝ, w * (x - m) ^ (2 : ℕ) =
    w * (x * x) - 2 * m * (w * x) + m ^ (2 : ℕ) * w by intros; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hmass]
  ring

/-- Additive prime statistics have an explicit diagonal robustness variance. -/
theorem eulerTiltVariance_linearStat (σ : ℝ) (N : ℕ)
    (a : ↥(Sieve.primeSubtypeLE N) → ℝ) :
    eulerTiltVariance σ N (linearStat a) =
      ∑ p : ↥(Sieve.primeSubtypeLE N), a p ^ (2 : ℕ) *
        (routeEEulerBernoulliProb σ p.1 * (1 - routeEEulerBernoulliProb σ p.1)) := by
  rw [eulerTiltVariance_eq_covariance, bernoulliCov_linearStat]
  simp only [pow_two]

/-- Euler-tilt expectation error is controlled by variance rather than second moment. -/
theorem eulerTilt_expectation_shift_sq_le_variance (δ : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) :
    (routeEEulerBernoulliExpBelow (1 + δ) N f -
        routeEEulerBernoulliExpBelow 1 N f) ^ (2 : ℕ) ≤
      routeEEulerTiltChiSquareBelow δ N * eulerTiltVariance 1 N f := by
  have h := routeEEulerBernoulliExpBelow_sub_sq_le δ N
    (fun S => f S - routeEEulerBernoulliExpBelow 1 N f)
  rw [eulerTiltExpectation_sub_const, eulerTiltExpectation_sub_const,
    sub_self, sub_zero] at h
  exact h

/-- Prime-clock energy yields a variance-sensitive certificate for every positive tilt. -/
theorem eulerTilt_expectation_shift_sq_le_primeClock (δ : ℝ≥0) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) :
    (routeEEulerBernoulliExpBelow (1 + (δ : ℝ)) N f -
        routeEEulerBernoulliExpBelow 1 N f) ^ (2 : ℕ) ≤
      (Real.exp (primeClockCutoffEnergy N ((δ : ℝ) / 2)) - 1) * eulerTiltVariance 1 N f := by
  exact (eulerTilt_expectation_shift_sq_le_variance δ N f).trans
    (mul_le_mul_of_nonneg_right (routeEEulerTiltChiSquareBelow_le_primeClock δ δ.property N)
      (eulerTiltVariance_nonneg 1 N f))

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTiltVariance_nonneg
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTiltExpectation_sub_const
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTiltVariance_eq_covariance
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTiltVariance_linearStat
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTilt_expectation_shift_sq_le_variance
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.eulerTilt_expectation_shift_sq_le_primeClock
