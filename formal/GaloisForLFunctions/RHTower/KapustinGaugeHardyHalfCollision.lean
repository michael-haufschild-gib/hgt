import GaloisForLFunctions.HTGeometry.BoundedPhaseHardyHalfToeplitz
import GaloisForLFunctions.RHTower.KapustinGaugeSmirnovCollision

/-!
# Half-power Hardy collision forced by a one-sided Kapustin gauge

The fourth-order Cayley-decaying bounded-phase construction upgrades either one-sided Kapustin
gauge assumption to a nonzero element of the fixed reciprocal-Gamma Toeplitz kernel whose forward
boundary has integrable square-root norm on the real line.
-/

open Complex MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact half-power Smirnov Toeplitz-kernel element forced by a nonnegative Kapustin gauge
weight. -/
noncomputable def kapustinSmirnovToeplitzHalfElement_of_rotated_nonnegative
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    SmirnovToeplitzHalfKernelElement kapustinToeplitzSymbol :=
  ((boundedPhaseSmirnovToeplitzHalfElement
      (kapustinNonnegativePhaseCircle Phi)
      (measurable_kapustinNonnegativePhaseCircle Phi)
      (abs_kapustinNonnegativePhaseCircle_le Phi)).mulLeftMultiplier Phi hPhi).congr
        (kapustinGauge_boundedPhase_symbol_eq_ae Phi hPhi hnonneg)

/-- Exact half-power Smirnov Toeplitz-kernel element forced by a nonpositive Kapustin gauge
weight.  This is the negative branch applied to the literal analytic gauge `-Phi`. -/
noncomputable def kapustinSmirnovToeplitzHalfElement_of_rotated_nonpositive
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonpos : ∀ᵐ x ∂volume, (kapustinRotatedGaugeQ Phi x).re ≤ 0) :
    SmirnovToeplitzHalfKernelElement kapustinToeplitzSymbol := by
  have hPhiNeg : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.neg.fn z ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := hPhi
    exact ⟨z, hz, neg_ne_zero.mpr hne⟩
  have hnonnegNeg :
      ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi.neg x).re := by
    filter_upwards [kapustinRotatedGaugeQ_neg_ae Phi, hnonpos] with x hx hle
    rw [hx]
    simpa using neg_nonneg.mpr hle
  exact kapustinSmirnovToeplitzHalfElement_of_rotated_nonnegative
    Phi.neg hPhiNeg hnonnegNeg

end

end RHTower
