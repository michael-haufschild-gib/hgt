import GaloisForLFunctions.HTGeometry.BoundedPhaseNPlusCircleL1
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzCircleL1
import GaloisForLFunctions.RHTower.KapustinGaugeOrientedNPlusCollision

open Complex MeasureTheory Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrable_forward_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    Integrable
      (kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
        Phi hPhi hnonneg).toKernelElement.forward.circleBoundary
      circleLebesgue := by
  let Iinner := diskMultiplierInnerFactor Phi hPhi
  let Oouter := diskMultiplierOuterFactor Phi hPhi
  have hOouter : IsOuterDiskMultiplier Oouter :=
    isOuterDiskMultiplier_diskMultiplierOuterFactor Phi hPhi
  have hOzero : ∀ z ∈ ball (0 : ℂ) 1, Oouter.fn z ≠ 0 := by
    intro z hz
    exact hOouter.ne_zero_on_disk
      (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  let hrootExists := Oouter.exists_squareRoot_of_zeroFree hOzero
  let Hroot : DiskMultiplier := Classical.choose hrootExists
  have hHsq : ∀ z ∈ ball (0 : ℂ) 1, Hroot.fn z ^ (2 : ℕ) = Oouter.fn z :=
    Classical.choose_spec hrootExists
  have hHnonzero : ∃ z ∈ ball (0 : ℂ) 1, Hroot.fn z ≠ 0 := by
    refine ⟨0, by simp [Metric.mem_ball], ?_⟩
    intro hzero
    have := hHsq 0 (by simp [Metric.mem_ball])
    rw [hzero] at this
    simp at this
    exact hOzero 0 (by simp [Metric.mem_ball]) this.symm
  let b := kapustinNonnegativePhaseCircle Phi
  let hb := measurable_kapustinNonnegativePhaseCircle Phi
  let hbound := abs_kapustinNonnegativePhaseCircle_le Phi
  let Kb := boundedPhaseSmirnovToeplitzNPlusOneElement b hb hbound
  let KH := Kb.mul_left_multiplier Hroot hHnonzero
  have hKb : Integrable Kb.toKernelElement.forward.circleBoundary circleLebesgue :=
    integrable_circleBoundary_boundedPhaseNPlusOne_forward b hb hbound
  have hKH : Integrable KH.toKernelElement.forward.circleBoundary circleLebesgue :=
    Kb.integrable_forward_circleBoundary_mul_left_multiplier Hroot hHnonzero hKb
  change Integrable KH.toKernelElement.forward.circleBoundary circleLebesgue
  exact hKH

theorem integrable_forward_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonpos : ∀ᵐ x ∂volume, (kapustinRotatedGaugeQ Phi x).re ≤ 0) :
    Integrable
      (kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
        Phi hPhi hnonpos).toKernelElement.forward.circleBoundary
      circleLebesgue := by
  have hPhiNeg : ∃ z ∈ ball (0 : ℂ) 1, Phi.neg.fn z ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := hPhi
    exact ⟨z, hz, neg_ne_zero.mpr hne⟩
  have hnonnegNeg :
      ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi.neg x).re := by
    filter_upwards [kapustinRotatedGaugeQ_neg_ae Phi, hnonpos]
      with x hx hle
    rw [hx]
    simpa using neg_nonneg.mpr hle
  change Integrable
    (kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
      Phi.neg hPhiNeg hnonnegNeg).toKernelElement.forward.circleBoundary
    circleLebesgue
  exact
    integrable_forward_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
      Phi.neg hPhiNeg hnonnegNeg

theorem integrable_reflected_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    Integrable
      (kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
        Phi hPhi hnonneg).toKernelElement.reflected.circleBoundary
      circleLebesgue := by
  let K := kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
    Phi hPhi hnonneg
  exact K.toKernelElement.integrable_reflected_circleBoundary
    (Filter.Eventually.of_forall norm_kapustinOneSidedToeplitzSymbol)
    (integrable_forward_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonnegative
      Phi hPhi hnonneg)

theorem integrable_reflected_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonpos : ∀ᵐ x ∂volume, (kapustinRotatedGaugeQ Phi x).re ≤ 0) :
    Integrable
      (kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
        Phi hPhi hnonpos).toKernelElement.reflected.circleBoundary
      circleLebesgue := by
  let K := kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
    Phi hPhi hnonpos
  exact K.toKernelElement.integrable_reflected_circleBoundary
    (Filter.Eventually.of_forall norm_kapustinOneSidedToeplitzSymbol)
    (integrable_forward_circleBoundary_kapustinSmirnovToeplitzNPlusElement_of_rotated_nonpositive
      Phi hPhi hnonpos)

end

end RHTower
