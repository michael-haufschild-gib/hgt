import GaloisForLFunctions.RHTower.XiPhysicalEndpointValuationCorrectionOddShuttle
import GaloisForLFunctions.RHTower.XiPrimeMarkedCycleGauge

/-!
# Corrected physical-endpoint cycle candidate for Route K

The correctly oriented unit--double refinement, together with its absolutely convergent
valuation correction, is source-defined at exact logarithmic prime ratios.  Its physical pair
dressing therefore supplies a literal, packet-independent symmetric edge kernel and closed
three-prime holonomies.  The finite determinant and quartic paired trace laws can be instantiated
on this candidate without Xi-zero enumeration.

Finite row balancing does not yet yield a cofinal operator.  Adding one prime changes every old
diagonal by exactly the negative new pair response; the total absolute diagonal shell is the
corresponding `ℓ¹` column mass.  Thus cofinal trace-ideal control requires a genuine summability or
renormalized-shell theorem.  This module proves the candidate and obstruction exactly; it asserts
neither holonomy nonvanishing nor trace-norm convergence.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Source-defined three-prime holonomy of the corrected physical-endpoint pair response. -/
def routeKPhysicalEndpointTriangleHolonomy
    (p q r : Nat.Primes) : ℝ :=
  xiPhysicalEndpointCompletedPairResponse p q *
    xiPhysicalEndpointCompletedPairResponse q r *
      xiPhysicalEndpointCompletedPairResponse r p

theorem routeKPhysicalEndpointTriangleHolonomy_cycle
    (p q r : Nat.Primes) :
    routeKPhysicalEndpointTriangleHolonomy p q r =
      routeKPhysicalEndpointTriangleHolonomy q r p := by
  simp [routeKPhysicalEndpointTriangleHolonomy]
  ring

theorem routeKPhysicalEndpointTriangleHolonomy_swap
    (p q r : Nat.Primes) :
    routeKPhysicalEndpointTriangleHolonomy p q r =
      routeKPhysicalEndpointTriangleHolonomy q p r := by
  rw [routeKPhysicalEndpointTriangleHolonomy,
    routeKPhysicalEndpointTriangleHolonomy,
    xiPhysicalEndpointCompletedPairResponse_symm p q,
    xiPhysicalEndpointCompletedPairResponse_symm q r,
    xiPhysicalEndpointCompletedPairResponse_symm r p]
  ring

/-- Three edges obtained by sampling the literal completed response on three marked primes. -/
def routeKPhysicalEndpointThreePrimeEdge
    (prime : Fin 3 → Nat.Primes) : Fin 3 → ℝ :=
  ![xiPhysicalEndpointCompletedPairResponse (prime 0) (prime 1),
    xiPhysicalEndpointCompletedPairResponse (prime 1) (prime 2),
    xiPhysicalEndpointCompletedPairResponse (prime 2) (prime 0)]

@[simp] theorem routeKPhysicalEndpointThreePrimeEdge_cycleProduct
    (prime : Fin 3 → Nat.Primes) :
    routeKPhysicalEndpointThreePrimeEdge prime 0 *
        routeKPhysicalEndpointThreePrimeEdge prime 1 *
          routeKPhysicalEndpointThreePrimeEdge prime 2 =
      routeKPhysicalEndpointTriangleHolonomy (prime 0) (prime 1) (prime 2) := by
  rfl

/-- Exact determinant response of the source-defined three-prime cycle candidate. -/
theorem routeKPhysicalEndpointThreePrimeCharacteristic_sub_edgeFlip
    (q : Fin 3 → ℝ) (prime : Fin 3 → Nat.Primes) (w : ℝ) :
    routeKThreePrimeCharacteristic q (routeKPhysicalEndpointThreePrimeEdge prime) w -
        routeKThreePrimeCharacteristic q
          (routeKThreePrimeEdgeFlip (routeKPhysicalEndpointThreePrimeEdge prime)) w =
      -4 * routeKPhysicalEndpointTriangleHolonomy (prime 0) (prime 1) (prime 2) := by
  rw [routeKThreePrimeCharacteristic_sub_edgeFlip]
  simp [routeKPhysicalEndpointThreePrimeEdge, routeKPhysicalEndpointTriangleHolonomy]
  ring

/-- Exact centered reflection-paired trace-cumulant response of the same source cycle. -/
theorem routeKPhysicalEndpointThreePrimePairedTracePower_four_sub_edgeFlip
    (q : Fin 3 → ℝ) (prime : Fin 3 → Nat.Primes) :
    routeKThreePrimePairedTracePower q (routeKPhysicalEndpointThreePrimeEdge prime) 4 -
        routeKThreePrimePairedTracePower q
          (routeKThreePrimeEdgeFlip (routeKPhysicalEndpointThreePrimeEdge prime)) 4 =
      32 * (q 0 + q 1 + q 2) *
        routeKPhysicalEndpointTriangleHolonomy (prime 0) (prime 1) (prime 2) := by
  rw [routeKThreePrimePairedTracePower_four_sub_edgeFlip]
  simp [routeKPhysicalEndpointThreePrimeEdge, routeKPhysicalEndpointTriangleHolonomy]
  ring

/-- Off-diagonal entries are already compatible under arbitrary packet changes. -/
theorem xiPhysicalEndpointCompletedBalancedCoupling_offDiagonal_packet_independent
    (P Q : Finset Nat.Primes) (p q : Nat.Primes) (hpq : p ≠ q) :
    xiPhysicalEndpointCompletedBalancedCoupling P p q =
      xiPhysicalEndpointCompletedBalancedCoupling Q p q := by
  simp [xiPhysicalEndpointCompletedBalancedCoupling, hpq]

/-- Adding one new prime changes every existing balanced diagonal by exactly the negative new
pair response. -/
theorem xiPhysicalEndpointCompletedBalancedCoupling_insert_diagonal_sub
    (P : Finset Nat.Primes) (p r : Nat.Primes)
    (hp : p ∈ P) (hr : r ∉ P) :
    xiPhysicalEndpointCompletedBalancedCoupling (insert r P) p p -
        xiPhysicalEndpointCompletedBalancedCoupling P p p =
      -xiPhysicalEndpointCompletedPairResponse p r := by
  have hpr : p ≠ r := by
    intro h
    apply hr
    rwa [← h]
  simp [xiPhysicalEndpointCompletedBalancedCoupling, hpr, hp, hr]

/-- Exact `ℓ¹` shell cost forced on the old diagonal when one prime is inserted. -/
theorem sum_abs_xiPhysicalEndpointCompletedBalancedCoupling_insert_diagonal_sub
    (P : Finset Nat.Primes) (r : Nat.Primes) (hr : r ∉ P) :
    ∑ p ∈ P,
        |xiPhysicalEndpointCompletedBalancedCoupling (insert r P) p p -
          xiPhysicalEndpointCompletedBalancedCoupling P p p| =
      ∑ p ∈ P, |xiPhysicalEndpointCompletedPairResponse p r| := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [xiPhysicalEndpointCompletedBalancedCoupling_insert_diagonal_sub P p r hp hr]
  exact abs_neg _

end

end RHTower
