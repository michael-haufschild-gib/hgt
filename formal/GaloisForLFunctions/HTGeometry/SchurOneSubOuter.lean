import GaloisForLFunctions.HTGeometry.AccretiveDiskMultiplierOuter
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor

/-!
# Outer regularization of a Schur factor

For every nonconstant Schur multiplier `theta`, the multiplier `1 - theta` is outer.  On the
unimodular part of the boundary its phase reflection is exactly `-conj theta`.  This is the
standard outer regularization that transfers an arbitrary inner factor into the outer side of a
Smirnov Toeplitz factorization without assuming finite Blaschke degree or boundary analyticity.
-/

open Complex MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `1 - theta` is outer for every nonconstant Schur multiplier. -/
theorem isOuterDiskMultiplier_one_sub_of_schur
    (theta : DiskMultiplier)
    (hschur : ∀ z ∈ ball (0 : ℂ) 1, ‖theta.fn z‖ ≤ 1)
    (hne : ∃ z ∈ ball (0 : ℂ) 1, theta.fn z ≠ 1) :
    IsOuterDiskMultiplier ((DiskMultiplier.const 1).sub theta) := by
  apply isOuterDiskMultiplier_of_re_nonneg
  · intro z hz
    change 0 ≤ (1 - theta.fn z).re
    simp only [Complex.sub_re, Complex.one_re]
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (hschur z hz))
  · obtain ⟨z, hz, hne⟩ := hne
    refine ⟨z, hz, ?_⟩
    change 1 - theta.fn z ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hne)

/-- Pointwise phase-reflection identity behind outer regularization. -/
theorem phaseReflection_one_sub_eq_neg_conj
    {theta : ℂ} (hunit : ‖theta‖ = 1) (hne : 1 - theta ≠ 0) :
    (starRingEnd ℂ) (1 - theta) / (1 - theta) =
      -(starRingEnd ℂ) theta := by
  have hmul : theta * (starRingEnd ℂ) theta = 1 := by
    rw [RCLike.mul_conj, hunit]
    norm_num
  have hmul' : (starRingEnd ℂ) theta * theta = 1 := by
    rw [mul_comm, hmul]
  apply (div_eq_iff hne).2
  calc
    (starRingEnd ℂ) (1 - theta) = 1 - (starRingEnd ℂ) theta := by simp
    _ = -(starRingEnd ℂ) theta + (starRingEnd ℂ) theta * theta := by
      rw [hmul']
      ring
    _ = (-(starRingEnd ℂ) theta) * (1 - theta) := by ring

/-- Boundary phase reflection of the outer regularizer is `-conj theta` almost everywhere. -/
theorem diskMultiplierPhaseReflectionSymbol_one_sub_ae
    (theta : DiskMultiplier)
    (hschur : ∀ z ∈ ball (0 : ℂ) 1, ‖theta.fn z‖ ≤ 1)
    (hunit : ∀ᵐ x ∂volume,
      ‖diskMultiplierLineBoundary theta x‖ = 1)
    (hne : ∃ z ∈ ball (0 : ℂ) 1, theta.fn z ≠ 1) :
    diskMultiplierPhaseReflectionSymbol ((DiskMultiplier.const 1).sub theta)
      =ᵐ[volume]
        fun x => -(starRingEnd ℂ) (diskMultiplierLineBoundary theta x) := by
  let A := (DiskMultiplier.const 1).sub theta
  have hAouter : IsOuterDiskMultiplier A :=
    isOuterDiskMultiplier_one_sub_of_schur theta hschur hne
  have hAne := diskMultiplierLineBoundary_ne_zero_ae A hAouter.exists_nonzero
  filter_upwards [diskMultiplierLineBoundary_sub_ae (DiskMultiplier.const 1) theta,
    diskMultiplierLineBoundary_const_ae 1, hunit, hAne] with x hsub hone htheta hA
  have hsubValue : diskMultiplierLineBoundary A x =
      1 - diskMultiplierLineBoundary theta x := by
    change diskMultiplierLineBoundary ((DiskMultiplier.const 1).sub theta) x = _
    rw [hsub, hone]
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hA, hsubValue]
  exact phaseReflection_one_sub_eq_neg_conj htheta (by simpa [hsubValue] using hA)

end

end GaloisForLFunctions.HTGeometry
