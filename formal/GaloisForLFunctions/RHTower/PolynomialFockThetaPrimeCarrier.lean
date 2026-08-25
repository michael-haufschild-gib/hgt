import GaloisForLFunctions.RHTower.PolynomialFockSharpPhaseTransition
import GaloisForLFunctions.RHTower.PolynomialMomentFockThetaTrace

/-!
# Pointed polynomial-Fock carrier for prime sampling and the completed theta trace

For every `m ≥ 4`, this module packages one literal moment-Fock Hilbert space with its normalized
all-prime sampler, bounded theta-trace evaluations, all bounded trace-moment functionals, and the
distinguished constant vector. The distinguished trace is exactly the completed Riemann zeta
function on the critical line after the fixed Fourier rescaling.
-/

namespace RHTower

noncomputable section

/-- One pointed Hilbert carrier simultaneously containing the normalized prime channel and the
completed theta trace germ. -/
structure PolynomialFockThetaPrimeCarrier (m : ℝ) (hm4 : 4 ≤ m) where
  primeSampler : MomentFock →L[ℂ] CriticalPrimeEllTwo
  traceAt : ℂ → MomentFock →L[ℂ] ℂ
  traceMoment : ℕ → MomentFock →L[ℂ] ℂ
  distinguished : MomentFock

/-- Canonical pointed carrier built from the polynomial moment-Fock realization. -/
def polynomialFockThetaPrimeCarrier (m : ℝ) (hm4 : 4 ≤ m) :
    PolynomialFockThetaPrimeCarrier m hm4 where
  primeSampler := polynomialCriticalPrimeSamplingOperator m hm4
  traceAt := polynomialMomentFockThetaTraceFunctional m (by linarith)
  traceMoment := polynomialMomentFockThetaMomentFunctional m (by linarith)
  distinguished := polynomialMomentFockOne m (by linarith)

@[simp] theorem polynomialFockThetaPrimeCarrier_primeSampler_apply
    (m : ℝ) (hm4 : 4 ≤ m) (f : MomentFock) (p : Nat.Primes) :
    (polynomialFockThetaPrimeCarrier m hm4).primeSampler f p =
      criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f := by
  rfl

@[simp] theorem polynomialFockThetaPrimeCarrier_traceAt_apply
    (m : ℝ) (hm4 : 4 ≤ m) (z : ℂ) (f : MomentFock) :
    (polynomialFockThetaPrimeCarrier m hm4).traceAt z f =
      polynomialMomentFockThetaTrace m (by linarith) f z := by
  rfl

@[simp] theorem polynomialFockThetaPrimeCarrier_traceMoment_apply
    (m : ℝ) (hm4 : 4 ≤ m) (n : ℕ) (f : MomentFock) :
    (polynomialFockThetaPrimeCarrier m hm4).traceMoment n f =
      iteratedDeriv n (polynomialMomentFockThetaTrace m (by linarith) f) 0 := by
  exact polynomialMomentFockThetaMomentFunctional_apply m (by linarith) n f

@[simp] theorem polynomialFockThetaPrimeCarrier_distinguished_evaluation
    (m : ℝ) (hm4 : 4 ≤ m) (z : ℂ) :
    polynomialMomentFockEvaluation m (by linarith) z
      (polynomialFockThetaPrimeCarrier m hm4).distinguished = 1 := by
  exact polynomialMomentFockEvaluation_one m (by linarith) z

/-- Exact completed critical trace at the distinguished point. -/
theorem completedRiemannZeta₀_critical_eq_polynomialFockThetaPrimeCarrier_trace
    (m : ℝ) (hm4 : 4 ≤ m) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) =
      (polynomialFockThetaPrimeCarrier m hm4).traceAt
        ((t / (4 * Real.pi) : ℝ) : ℂ)
        (polynomialFockThetaPrimeCarrier m hm4).distinguished / 2 := by
  rw [polynomialFockThetaPrimeCarrier_traceAt_apply]
  exact completedRiemannZeta₀_critical_eq_polynomialMomentFockThetaTrace_one
    m (by linarith) t

/-- Prime channel is compact exactly in the superquartic regime. -/
theorem polynomialFockThetaPrimeCarrier_primeSampler_isCompactOperator_iff
    {m : ℝ} (hm4 : 4 ≤ m) :
    IsCompactOperator (polynomialFockThetaPrimeCarrier m hm4).primeSampler ↔ 4 < m := by
  exact polynomialCriticalPrimeSamplingOperator_isCompactOperator_iff hm4

end

end RHTower
