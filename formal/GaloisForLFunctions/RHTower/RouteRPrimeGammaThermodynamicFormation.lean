import GaloisForLFunctions.RHTower.RouteRPrimeGammaPoissonHiddenHistory
import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityFisherBound

/-!
# Thermodynamic meaning of reflected Gamma formation

Exponentiating the forward and reflected Gamma formation laws produces two positive Poisson
rates. Their logarithmic thermodynamic affinity is exactly the signed prime Gamma Bockstein.
Consequently the Poisson hidden-history density is literal entropy production, while the
three-slot exchangeability defect is one half of the squared affinity.

Thus completion history, stochastic exchangeability, and nonequilibrium thermodynamics retain
the same horizontal current in different metrics. Detailed balance at every Xi divisor is
equivalent to the Riemann hypothesis. The equivalence identifies the required equilibrium law;
it does not assert that arithmetic source dynamics supplies detailed balance.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open scoped NNReal

/-- The signed prime Gamma Bockstein is the log-rate affinity of the two reflected Poisson
formations. -/
theorem routeRPrimeGammaPoisson_thermodynamicAffinity_eq_bockstein
    (t : ℝ) (p : Nat.Primes) :
    thermodynamicAffinity
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) =
      primeGammaCofinalBocksteinCoefficient t p := by
  rw [thermodynamicAffinity]
  change Real.log
    (Real.exp (routeRPrimeGammaForwardFormationLaw t p 0) /
      Real.exp (routeRPrimeGammaReflectedFormationLaw t p 0)) = _
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, Real.log_exp]
  rw [primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression]
  simp [routeRPrimeGammaForwardFormationLaw,
    routeRPrimeGammaReflectedFormationLaw]
  ring

/-- Hidden Poisson formation history is exactly edgewise thermodynamic entropy production. -/
theorem routeRPrimeGammaPoissonHiddenHistoryDensity_eq_entropyProduction
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPoissonHiddenHistoryDensity t p =
      entropyProductionValue
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) := by
  rfl

/-- The three-slot exchangeability defect is one half of the squared thermodynamic affinity. -/
theorem routeRPrimeGammaFormationDefect_eq_affinity_sq
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaFormationDefect t p =
      thermodynamicAffinity
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) ^ 2 / 2 := by
  rw [routeRPrimeGammaPoisson_thermodynamicAffinity_eq_bockstein,
    routeRPrimeGammaFormationDefect_eq_bockstein_sq]

/-- Thermodynamic uncertainty: Poisson hidden-history density dominates the symmetric quadratic
current cost of the reflected rates. -/
theorem routeRPrimeGammaPoisson_pseudoEntropy_le_hiddenHistoryDensity
    (t : ℝ) (p : Nat.Primes) :
    pseudoEntropyProductionValue
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) ≤
      routeRPrimeGammaPoissonHiddenHistoryDensity t p := by
  rw [routeRPrimeGammaPoissonHiddenHistoryDensity_eq_entropyProduction]
  apply pseudoEntropyProductionValue_le_entropyProductionValue
  · exact_mod_cast routeRPrimeGammaForwardPoissonRate_pos t p
  · exact_mod_cast routeRPrimeGammaReflectedPoissonRate_pos t p

/-- Reflected Poisson formation has zero entropy production exactly at neutral horizontal grade. -/
theorem routeRPrimeGammaPoisson_entropyProduction_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    entropyProductionValue
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) = 0 ↔
      t = 0 := by
  rw [← routeRPrimeGammaPoissonHiddenHistoryDensity_eq_entropyProduction,
    routeRPrimeGammaPoissonHiddenHistoryDensity_eq_zero_iff]

/-- Three-slot exchangeability and thermodynamic detailed balance are the same reflected Gamma
condition. -/
theorem routeRPrimeGamma_threeSlotExchangeable_iff_detailedBalance
    (t : ℝ) (p : Nat.Primes) :
    ThreeSlotExchangeable
        (routeRPrimeGammaForwardFormationLaw t p)
        (routeRPrimeGammaReflectedFormationLaw t p) ↔
      entropyProductionValue
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) = 0 := by
  rw [routeRPrimeGamma_threeSlotExchangeable_iff,
    routeRPrimeGammaPoisson_entropyProduction_eq_zero_iff]

/-- Every Xi divisor is locally detailed-balanced at one retained prime. -/
def RouteRPrimeGammaXiPoissonDetailedBalanced (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    entropyProductionValue
      (routeRPrimeGammaForwardPoissonRate ((rho : ℂ).re - 1 / 2) p : ℝ)
      (routeRPrimeGammaReflectedPoissonRate ((rho : ℂ).re - 1 / 2) p : ℝ) = 0

/-- At an Xi divisor, local detailed balance is exactly critical-line placement. -/
theorem routeRPrimeGammaXiPoisson_detailedBalance_iff_re_eq_half
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    entropyProductionValue
        (routeRPrimeGammaForwardPoissonRate ((rho : ℂ).re - 1 / 2) p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate ((rho : ℂ).re - 1 / 2) p : ℝ) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaPoisson_entropyProduction_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- Detailed balance of every reflected Xi formation at one prime is equivalent to RH. -/
theorem routeRPrimeGammaXiPoissonDetailedBalanced_iff_riemannHypothesis
    (p : Nat.Primes) :
    RouteRPrimeGammaXiPoissonDetailedBalanced p ↔ RiemannHypothesis := by
  rw [← routeRPrimeGammaXiPoissonHistoryNeutral_iff_riemannHypothesis p]
  unfold RouteRPrimeGammaXiPoissonDetailedBalanced
    RouteRPrimeGammaXiPoissonHistoryNeutral
  apply forall_congr'
  intro rho
  rw [routeRPrimeGammaXiPoissonHiddenHistoryDensity,
    routeRPrimeGammaPoissonHiddenHistoryDensity_eq_entropyProduction]

end RHTower
