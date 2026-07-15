import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeUnit
import GaloisForLFunctions.HTGeometry.AlmostDisjointIsodivisorialFrame

/-!
# Isodivisorial continuation along exponent-zero gauge leaves

The locally normal Euler-ratio product is a holomorphic unit throughout the positive half-plane.
Multiplying any meromorphic continuation by this unit therefore produces the canonical continued
source in the gauge-changed phase and preserves every local signed meromorphic order.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- The canonical continuation obtained by multiplying a continued Euler source by its
exponent-zero Euler-ratio unit. -/
noncomputable def exponentZeroGaugeContinuedSource
    (eta omega : PrimePhase Nat.Primes) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  exponentZeroEulerGaugeUnit eta omega s * f s

/-- The exponent-zero Euler-ratio unit is analytic at every positive-half-plane point. -/
theorem analyticAt_exponentZeroEulerGaugeUnit
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    {z : ℂ} (hz : z ∈ positiveHalfPlane) :
    AnalyticAt ℂ (exponentZeroEulerGaugeUnit eta omega) z := by
  exact (differentiableOn_exponentZeroEulerGaugeUnit eta omega homega).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

/-- A meromorphic continuation remains meromorphic after an exponent-zero gauge change. -/
theorem meromorphicAt_exponentZeroGaugeContinuedSource
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ positiveHalfPlane)
    (hf : MeromorphicAt f z) :
    MeromorphicAt (exponentZeroGaugeContinuedSource eta omega f) z := by
  exact (analyticAt_exponentZeroEulerGaugeUnit eta omega homega hz).meromorphicAt.mul hf

/-- The construction transports a meromorphic continuation across the whole positive half-plane. -/
theorem meromorphicOn_exponentZeroGaugeContinuedSource
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    {f : ℂ → ℂ} (hf : MeromorphicOn f positiveHalfPlane) :
    MeromorphicOn (exponentZeroGaugeContinuedSource eta omega f) positiveHalfPlane := by
  intro z hz
  exact meromorphicAt_exponentZeroGaugeContinuedSource eta omega homega hz (hf z hz)

/-- The complete signed divisor is unchanged at every positive-half-plane point. -/
theorem meromorphicOrderAt_exponentZeroGaugeContinuedSource_eq
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ positiveHalfPlane) :
    meromorphicOrderAt (exponentZeroGaugeContinuedSource eta omega f) z =
      meromorphicOrderAt f z := by
  exact meromorphicOrderAt_mul_analyticUnit_eq
    (analyticAt_exponentZeroEulerGaugeUnit eta omega homega hz)
    (exponentZeroEulerGaugeUnit_ne_zero eta omega homega hz)

/-- Orbit-level form: every exponent-zero gauge preserves every local signed divisor order. -/
theorem exponentZeroGauge_completePositiveHalfPlaneDivisor_eq
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    (f : ℂ → ℂ) :
    ∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt (exponentZeroGaugeContinuedSource eta omega f) z =
        meromorphicOrderAt f z := by
  intro z hz
  exact meromorphicOrderAt_exponentZeroGaugeContinuedSource_eq eta omega homega f hz

end

end GaloisForLFunctions.HTGeometry
