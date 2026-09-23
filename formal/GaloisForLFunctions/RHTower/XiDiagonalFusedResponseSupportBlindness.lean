import GaloisForLFunctions.RHTower.XiAperturePhysicalEndpointResponseRenormalization
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric

/-!
# Support-blindness of the diagonal unit--double response lift

The source-defined unit--double current has exactly the opposite non-trace-class coefficient to
the physical endpoint source.  This file proves the stronger vector statement: their cancellation
holds for arbitrary prime-labelled vectors in every real module, before any aperture geometry or
prime joining is used.

For the true clipped-aperture Hilbert carrier, the completed diagonal current is therefore exactly
the inverse-square remainder carrier.  This is a useful no-go: the diagonal current cannot itself
be the RH-bearing joined response, because its cancellation is independent of the locations and
correlations of the prime support.  A viable completed response must retain this source-forced
linear countercurrent while adding a genuinely off-diagonal prime coupling.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Universal diagonal response cancellation.**  The physical endpoint source plus the
unit--double fused response current is the inverse-square remainder for arbitrary prime-labelled
vectors.  No inner product, aperture, or property of the prime support is used. -/
theorem physicalEndpoint_add_unitDoubleFusedResponse_sum_eq_remainder
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Finset Nat.Primes) (v : Nat.Primes → E) :
    (∑ p ∈ P, physicalPrimeEndpointWeight p • v p) +
        (∑ p ∈ P, xiUnitDoubleFusedPrimeResponseCurrent p • v p) =
      ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p • v p := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← add_smul]
  congr 1
  linarith [physicalPrimeEndpointWeight_eq_neg_fusedResponse_add_remainder p]

/-- The clocked unit--double response current carried by the actual centered clipped prime
apertures. -/
def xiUnitDoubleFusedPrimeResponseApertureCarrier
    (P : Finset Nat.Primes) (A m k : ℝ) : XiPhysicalApertureL2 :=
  ∑ p ∈ P, xiUnitDoubleFusedPrimeResponseCurrent p •
    xiPhysicalPrimeLogCenteredApertureCarrier A m k p

/-- The trace-class endpoint-response remainder carried by the actual centered clipped prime
apertures. -/
def xiPhysicalEndpointResponseRemainderApertureCarrier
    (P : Finset Nat.Primes) (A m k : ℝ) : XiPhysicalApertureL2 :=
  ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p •
    xiPhysicalPrimeLogCenteredApertureCarrier A m k p

/-- On the true physical aperture Hilbert space, adjoining the diagonal fused response current
cancels the whole prime-harmonic endpoint channel before taking a norm. -/
theorem xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogAggregateApertureCarrier P A m k +
        xiUnitDoubleFusedPrimeResponseApertureCarrier P A m k =
      xiPhysicalEndpointResponseRemainderApertureCarrier P A m k := by
  exact physicalEndpoint_add_unitDoubleFusedResponse_sum_eq_remainder P
    (fun p => xiPhysicalPrimeLogCenteredApertureCarrier A m k p)

/-- Exact energy form of the support-blind cancellation.  The norm of the completed diagonal
carrier is literally the norm of the inverse-square remainder carrier. -/
theorem norm_sq_xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder
    (P : Finset Nat.Primes) (A m k : ℝ) :
    ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k +
        xiUnitDoubleFusedPrimeResponseApertureCarrier P A m k‖ ^ (2 : ℕ) =
      ‖xiPhysicalEndpointResponseRemainderApertureCarrier P A m k‖ ^ (2 : ℕ) := by
  rw [xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder]

end

end RHTower

