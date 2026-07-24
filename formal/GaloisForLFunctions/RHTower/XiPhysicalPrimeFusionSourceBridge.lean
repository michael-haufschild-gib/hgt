import GaloisForLFunctions.RHTower.XiDiagonalFusedResponseSupportBlindness
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureDiagonalBudget

/-!
# `HGS29` source bridge for the physical prime-log fusion carrier

The fusion source `(PFK2)` of `xi-physical-prime-log-aperture-fusion-cross-kernel` is identified with
the existing `HGS29`/`AC25` unit--double Xi response current: the aggregate aperture carrier equals the
negated fused-response carrier plus a trace-class remainder carrier, and that remainder carrier has
`L²` norm at most `√A` times the summable remainder weight sum
`∑_p log p / (p(p+1))`.  Thus the source is the response current up to a carrier of controlled norm.
-/

open Real

namespace RHTower

/-- **`HGS29` source bridge.**  The physical fusion source carrier `(PFK2)` is exactly the negated
unit--double Xi response-current fusion plus the trace-class remainder fusion — the identification of
the fusion source with the existing `HGS29`/`AC25` response carrier.  Immediate from the additive
support-blind cancellation `xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder`. -/
theorem xiPhysicalPrimeLogAggregateApertureCarrier_eq_neg_fusedResponse_add_remainder
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogAggregateApertureCarrier P A m k =
      -xiUnitDoubleFusedPrimeResponseApertureCarrier P A m k +
        xiPhysicalEndpointResponseRemainderApertureCarrier P A m k := by
  have h := xiPhysicalPrimeLogAggregate_add_fusedResponse_eq_remainder P A m k
  rw [← h]; abel

/-- The trace-class remainder carrier has norm at most `√A` times the summable remainder weight sum:
the fusion source and the response current differ by a carrier of controlled `L²` norm. -/
theorem norm_remainderApertureCarrier_le {A : ℝ} (hA : 0 < A) (m k : ℝ)
    (P : Finset Nat.Primes) :
    ‖xiPhysicalEndpointResponseRemainderApertureCarrier P A m k‖
      ≤ Real.sqrt A * ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p := by
  rw [xiPhysicalEndpointResponseRemainderApertureCarrier]
  calc ‖∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p •
          xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖
      ≤ ∑ p ∈ P, ‖xiPhysicalEndpointResponseWeightRemainder p •
          xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ := norm_sum_le _ _
    _ = ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p *
          ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ := by
        apply Finset.sum_congr rfl; intro p _
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (xiPhysicalEndpointResponseWeightRemainder_pos p).le]
    _ ≤ ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p * Real.sqrt A := by
        apply Finset.sum_le_sum; intro p _
        exact mul_le_mul_of_nonneg_left (norm_centeredCarrier_le hA m k p)
          (xiPhysicalEndpointResponseWeightRemainder_pos p).le
    _ = Real.sqrt A * ∑ p ∈ P, xiPhysicalEndpointResponseWeightRemainder p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring

end RHTower
