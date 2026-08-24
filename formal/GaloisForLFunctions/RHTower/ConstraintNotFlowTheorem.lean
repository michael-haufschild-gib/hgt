import GaloisForLFunctions.HTGeometry.KroneckerFlow
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.RHTower.PrimeScreenAlmostPeriodicNoGo
import GaloisForLFunctions.RHTower.SigmaOrbit
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions

/-- Explicit affine one-parameter flow through the FE reflection.  This records the correction
that order two alone does not prohibit embedding an involution in an `ℝ`-flow. -/
def sigmaAffineFlow (t : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + Complex.exp ((Real.pi * t : ℝ) * Complex.I) * (z - 1 / 2)

@[simp] theorem sigmaAffineFlow_zero (z : ℂ) : sigmaAffineFlow 0 z = z := by
  simp [sigmaAffineFlow]

theorem sigmaAffineFlow_add (s t : ℝ) (z : ℂ) :
    sigmaAffineFlow (s + t) z = sigmaAffineFlow s (sigmaAffineFlow t z) := by
  rw [sigmaAffineFlow, sigmaAffineFlow, sigmaAffineFlow]
  rw [show (Real.pi * (s + t) : ℝ) = Real.pi * s + Real.pi * t by ring]
  push_cast
  rw [show ((Real.pi : ℂ) * (s : ℂ) + (Real.pi : ℂ) * (t : ℂ)) * Complex.I =
    (Real.pi : ℂ) * (s : ℂ) * Complex.I +
      (Real.pi : ℂ) * (t : ℂ) * Complex.I by ring, Complex.exp_add]
  ring

theorem sigmaAffineFlow_one (z : ℂ) : sigmaAffineFlow 1 z = sigma z := by
  rw [sigmaAffineFlow]
  norm_num [sigma]
  ring

/-- Corrected exact formal theorem behind “constraint, not flow”.  The canonical prime flow is
a continuous Kronecker flow with prime-log Fourier frequencies and dense finite apertures, but no
bounded continuous prime-screen symbol or finite-measure observable can reproduce completed Xi.
Xi is FE-reflection constrained.  The final field prevents the invalid stronger inference that an
order-two reflection cannot itself sit inside some one-parameter flow. -/
structure ConstraintNotFlowPackage : Prop where
  axisPrimeFrequency : ∀ (p : Nat.Primes) (k : ℤ),
    primeLogFrequency (Finsupp.single p k) = (k : ℝ) * Real.log (p : ℕ)
  finiteCharacterNoResonance : ∀ m : Nat.Primes →₀ ℤ,
    primeLogFrequency m = 0 ↔ m = 0
  primeFlowGroupLaw : ∀ s t : ℝ,
    RHTower.primeKronecker (s + t) =
      RHTower.primeKronecker s * RHTower.primeKronecker t
  primeFlowContinuous : Continuous RHTower.primeKronecker
  finitePrimeApertureDense : ∀ (N : ℕ) (θ : primesLE N → ℝ) {ε : ℝ},
    0 < ε → ∃ t : ℝ, ∀ p : primesLE N,
      ‖expChar (Real.log ((p : Nat.Primes) : ℕ)) t -
        Complex.exp ((θ p : ℝ) * Complex.I)‖ < ε
  noBoundedPrimeScreenXi :
    ¬ ∃ g : RHTower.PrimeTorus → ℂ, Continuous g ∧
      ∀ t : ℝ, g (RHTower.primeKronecker t) = RHTower.XiC (t : ℂ)
  noFiniteMeasurePrimeObservableXi : ∀
    (μ : Measure RHTower.PrimeTorus) [IsFiniteMeasure μ],
    ¬ ∃ f : RHTower.PrimeTorus → ℂ, Continuous f ∧
      ∀ t : ℝ, (∫ z, f (RHTower.primeKronecker t * z) ∂μ) = RHTower.XiC (t : ℂ)
  completedFunctionalEquation : ∀ {s : ℂ}, 0 < s.re → 0 < (1 - s).re →
    VorosClosedForm.xiFun (1 - s) = VorosClosedForm.xiFun s
  feReflectionInvolutive : ∀ s : ℂ, sigma (sigma s) = s
  feReflectionFixedPoint : ∀ s : ℂ, sigma s = s ↔ s = 1 / 2
  feSchwarzReflectionInvolutive : ∀ s : ℂ, sigmaConj (sigmaConj s) = s
  criticalLineFixedLocus : ∀ s : ℂ, sigmaConj s = s ↔ s.re = 1 / 2
  reflectionFlowEmbedding :
    (∀ z : ℂ, sigmaAffineFlow 0 z = z) ∧
    (∀ s t z, sigmaAffineFlow (s + t) z = sigmaAffineFlow s (sigmaAffineFlow t z)) ∧
    (∀ z : ℂ, sigmaAffineFlow 1 z = sigma z)

/-- Closed unconditional corrected constraint/prime-flow theorem. -/
theorem constraintNotFlow_unconditional : ConstraintNotFlowPackage := by
  refine {
    axisPrimeFrequency := primeLogFrequency_single
    finiteCharacterNoResonance := primeLogFrequency_eq_zero_iff
    primeFlowGroupLaw := RHTower.primeKronecker_add
    primeFlowContinuous := RHTower.continuous_primeKronecker
    finitePrimeApertureDense := primeTorus_kronecker_dense
    noBoundedPrimeScreenXi := RHTower.not_exists_primeScreen_symbol_eq_XiC
    noFiniteMeasurePrimeObservableXi := RHTower.not_exists_primeScreen_observable_eq_XiC
    completedFunctionalEquation := SeamSplit.xiFun_one_sub
    feReflectionInvolutive := sigma_involutive
    feReflectionFixedPoint := sigma_fixed_iff_eq_half
    feSchwarzReflectionInvolutive := sigmaConj_involutive
    criticalLineFixedLocus := sigmaConj_fixed_iff_critical
    reflectionFlowEmbedding := ⟨sigmaAffineFlow_zero, sigmaAffineFlow_add, sigmaAffineFlow_one⟩ }

end GaloisForLFunctions
