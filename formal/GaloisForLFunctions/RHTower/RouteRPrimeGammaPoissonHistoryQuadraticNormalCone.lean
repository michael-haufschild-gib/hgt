import GaloisForLFunctions.RHTower.RouteRPrimeGammaThermodynamicFormation
import GaloisForLFunctions.RHTower.SourceHorizontalWoldNeutralJetBridge

/-!
# Quadratic normal cone of hidden prime--Gamma formation history

The reflected prime--Gamma Poisson history was already known to retain a positive defect away
from neutral horizontal grade while visible occupancy saturates.  This module determines its
previously uncomputed local normal form at the neutral wall.

The history density factors into the signed rate difference and the Gamma Bockstein.  Both factors
vanish to first order, so their product has a positive quadratic tangent coefficient.  After the
uniformly bounded neutral-jet gauge, that coefficient is exactly the square of the literal
depth-one Wold source coefficient, times one positive occupancy factor.

Thus completion-history information is not merely another zero-locus classifier: its quadratic
normal coefficient is a coefficient-faithful arithmetic metric.  Any completion that erases this data
cannot preserve the Wold source.  No RH assertion is made here.
-/

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Difference of the two reflected positive Poisson formation rates. -/
def routeRPrimeGammaPoissonRateDifference (t : ℝ) (p : Nat.Primes) : ℝ :=
  (routeRPrimeGammaForwardPoissonRate t p : ℝ) -
    (routeRPrimeGammaReflectedPoissonRate t p : ℝ)

/-- Positive quadratic coefficient of hidden formation history at neutral grade. -/
def routeRPrimeGammaPoissonHistoryQuadraticCoefficient (p : Nat.Primes) : ℝ :=
  4 * primeActivationOccupancyFisherDensity p ^ 2 * Real.log (p : ℝ) ^ 2 *
    Real.exp (-primeActivationOccupancyFisherDensity p)

/-- Hidden history is the product of the reflected rate current and its thermodynamic affinity,
which is the signed Gamma Bockstein. -/
theorem routeRPrimeGammaPoissonHiddenHistoryDensity_eq_rateDifference_mul_bockstein
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPoissonHiddenHistoryDensity t p =
      routeRPrimeGammaPoissonRateDifference t p *
        primeGammaCofinalBocksteinCoefficient t p := by
  rw [routeRPrimeGammaPoissonHiddenHistoryDensity, rateJeffreys]
  change routeRPrimeGammaPoissonRateDifference t p *
      thermodynamicAffinity
        (routeRPrimeGammaForwardPoissonRate t p : ℝ)
        (routeRPrimeGammaReflectedPoissonRate t p : ℝ) = _
  rw [routeRPrimeGammaPoisson_thermodynamicAffinity_eq_bockstein]

@[simp] theorem routeRPrimeGammaPoissonRateDifference_zero (p : Nat.Primes) :
    routeRPrimeGammaPoissonRateDifference 0 p = 0 := by
  simp [routeRPrimeGammaPoissonRateDifference,
    routeRPrimeGammaForwardPoissonRate,
    routeRPrimeGammaReflectedPoissonRate,
    routeRPrimeGammaForwardFormationLaw,
    routeRPrimeGammaReflectedFormationLaw,
    primeGammaPhysicalRotationDeterminant]

/-- First neutral jet of the forward positive Poisson rate. -/
theorem hasDerivAt_routeRPrimeGammaForwardPoissonRate_zero (p : Nat.Primes) :
    HasDerivAt (fun t : ℝ => (routeRPrimeGammaForwardPoissonRate t p : ℝ))
      (-primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
        Real.exp (-primeActivationOccupancyFisherDensity p)) 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpow : HasDerivAt (fun t : ℝ => (p : ℝ) ^ t) (Real.log (p : ℝ)) 0 := by
    apply ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_rpow hp0).congr_deriv
    simp
  have h := (hpow.neg.const_mul (primeActivationOccupancyFisherDensity p)).exp
  have hfun :
      (fun t : ℝ => (routeRPrimeGammaForwardPoissonRate t p : ℝ)) =
        (fun t : ℝ => Real.exp
          (primeActivationOccupancyFisherDensity p * (-((p : ℝ) ^ t)))) := by
    funext t
    rfl
  rw [hfun]
  convert h using 1
  · funext t
    congr 1
  · simp
    ring

/-- First neutral jet of the reflected positive Poisson rate. -/
theorem hasDerivAt_routeRPrimeGammaReflectedPoissonRate_zero (p : Nat.Primes) :
    HasDerivAt (fun t : ℝ => (routeRPrimeGammaReflectedPoissonRate t p : ℝ))
      (primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
        Real.exp (-primeActivationOccupancyFisherDensity p)) 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpow : HasDerivAt (fun t : ℝ => (p : ℝ) ^ (-t)) (-Real.log (p : ℝ)) 0 := by
    have h := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg.const_rpow hp0)
    convert h using 1 <;> simp
  have h := (hpow.neg.const_mul (primeActivationOccupancyFisherDensity p)).exp
  have hfun :
      (fun t : ℝ => (routeRPrimeGammaReflectedPoissonRate t p : ℝ)) =
        (fun t : ℝ => Real.exp
          (primeActivationOccupancyFisherDensity p * (-((p : ℝ) ^ (-t))))) := by
    funext t
    rfl
  rw [hfun]
  convert h using 1
  · funext t
    congr 1
  · simp
    ring

/-- The reflected Poisson rate current has a nonzero first neutral jet. -/
theorem hasDerivAt_routeRPrimeGammaPoissonRateDifference_zero (p : Nat.Primes) :
    HasDerivAt (fun t : ℝ => routeRPrimeGammaPoissonRateDifference t p)
      (-2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
        Real.exp (-primeActivationOccupancyFisherDensity p)) 0 := by
  have h := (hasDerivAt_routeRPrimeGammaForwardPoissonRate_zero p).sub
    (hasDerivAt_routeRPrimeGammaReflectedPoissonRate_zero p)
  apply h.congr_deriv
  ring

/-- **Quadratic source-normal law.** Hidden formation-history entropy has a nondegenerate
quadratic normal cone at neutral grade, with an explicit positive arithmetic coefficient. -/
theorem tendsto_routeRPrimeGammaPoissonHiddenHistoryDensity_div_sq_zero
    (p : Nat.Primes) :
    Tendsto (fun t : ℝ =>
      routeRPrimeGammaPoissonHiddenHistoryDensity t p / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (routeRPrimeGammaPoissonHistoryQuadraticCoefficient p)) := by
  have hrate :=
    (hasDerivAt_routeRPrimeGammaPoissonRateDifference_zero p).tendsto_slope_zero
  have hrate' : Tendsto (fun t : ℝ =>
      routeRPrimeGammaPoissonRateDifference t p / t)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
        Real.exp (-primeActivationOccupancyFisherDensity p))) := by
    simpa [div_eq_inv_mul] using hrate
  have hbockstein :=
    (hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero p).tendsto_slope_zero
  have hbockstein' : Tendsto (fun t : ℝ =>
      primeGammaCofinalBocksteinCoefficient t p / t)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ))) := by
    simpa [primeGammaCofinalBocksteinCoefficient,
      primeActivationOccupancyFisherTwist, div_eq_inv_mul] using hbockstein
  have hmul := hrate'.mul hbockstein'
  have hmul' : Tendsto (fun t : ℝ =>
      (routeRPrimeGammaPoissonRateDifference t p / t) *
        (primeGammaCofinalBocksteinCoefficient t p / t))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (routeRPrimeGammaPoissonHistoryQuadraticCoefficient p)) := by
    convert hmul using 1
    simp only [routeRPrimeGammaPoissonHistoryQuadraticCoefficient]
    ring
  refine hmul'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  rw [routeRPrimeGammaPoissonHiddenHistoryDensity_eq_rateDifference_mul_bockstein]
  field_simp [ht]

/-- The source-normal quadratic coefficient is strictly positive at every ordinary prime. -/
theorem routeRPrimeGammaPoissonHistoryQuadraticCoefficient_pos (p : Nat.Primes) :
    0 < routeRPrimeGammaPoissonHistoryQuadraticCoefficient p := by
  rw [routeRPrimeGammaPoissonHistoryQuadraticCoefficient]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hF : 0 < primeActivationOccupancyFisherDensity p := by
    rw [primeActivationOccupancyFisherDensity_eq]
    positivity
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  positivity

/-- The retained history has a genuine positive quadratic lower wall near neutral grade. -/
theorem eventually_routeRPrimeGammaPoissonHiddenHistoryDensity_quadratic_lower
    (p : Nat.Primes) :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      routeRPrimeGammaPoissonHistoryQuadraticCoefficient p / 2 * t ^ 2 <
        routeRPrimeGammaPoissonHiddenHistoryDensity t p := by
  have hpos := routeRPrimeGammaPoissonHistoryQuadraticCoefficient_pos p
  have hhalf : routeRPrimeGammaPoissonHistoryQuadraticCoefficient p / 2 <
      routeRPrimeGammaPoissonHistoryQuadraticCoefficient p := by
    linarith
  have hratio := (tendsto_order.1
    (tendsto_routeRPrimeGammaPoissonHiddenHistoryDensity_div_sq_zero p)).1 _ hhalf
  filter_upwards [hratio, self_mem_nhdsWithin] with t hratio ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  have htSq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  calc
    routeRPrimeGammaPoissonHistoryQuadraticCoefficient p / 2 * t ^ 2 <
        (routeRPrimeGammaPoissonHiddenHistoryDensity t p / t ^ 2) * t ^ 2 :=
      mul_lt_mul_of_pos_right hratio htSq
    _ = routeRPrimeGammaPoissonHiddenHistoryDensity t p := by
      field_simp [ht]

/-- **Coefficient-faithful quadratic bridge.** The formation-history quadratic normal coefficient
is the literal depth-one Wold source coefficient squared, through the bounded neutral-jet gauge and
a positive occupancy factor. -/
theorem routeRPrimeGammaPoissonHistoryQuadraticCoefficient_mul_gauge_sq
    (p : Nat.Primes) :
    routeRPrimeGammaPoissonHistoryQuadraticCoefficient p *
        sourceHorizontalWoldNeutralJetGauge p ^ 2 =
      Real.exp (-primeActivationOccupancyFisherDensity p) * woldCoeff 1 p ^ 2 := by
  rw [routeRPrimeGammaPoissonHistoryQuadraticCoefficient]
  have hbridge := sourceHorizontalWoldNeutralJetGauge_mul_bocksteinJet p
  rw [← hbridge]
  ring

end

end RHTower
