import GaloisForLFunctions.HTGeometry.LeafUniqueness

/-!
# The leaves are extreme points of the complete-moment fiber

If a leaf is a mixture of representing probability measures then each component is dominated by a
multiple of the leaf, hence carried by the same denominator fiber; and a representing measure carried
by that fiber *is* the leaf.  So the mixture was trivial.

Extremality is therefore a corollary of uniqueness, not an independent convexity argument.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A component of a mixture equal to a leaf is carried by the leaf's fiber. -/
theorem carried_of_mixture_eq_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {μ ν : Measure ℝ} {a b : ENNReal} (ha : a ≠ 0)
    (hmix : (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) = a • μ + b • ν) :
    μ ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 := by
  have hzero := nevLeaf_finite_carried h h0b h0 tau
  rw [hmix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul] at hzero
  have hsum := (add_eq_zero.mp hzero).1
  rcases mul_eq_zero.mp hsum with hc | hc
  · exact absurd hc ha
  · exact hc

/-- **Each leaf is an extreme point of the complete-moment fiber.** -/
theorem nevLeaf_eq_of_mixture (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {a b : ENNReal} (ha : a ≠ 0)
    (hmix : (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) = a • μ + b • ν) :
    μ = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) :=
  nevLeaf_unique h h0b h0 tau hmom
    (carried_of_mixture_eq_nevLeaf h h0b h0 tau ha hmix)

/-- **The leaf at infinity is extreme too.** -/
theorem nevLeaf_infinity_eq_of_mixture (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {a b : ENNReal} (ha : a ≠ 0)
    (hmix : (nevLeaf h h0b h0 ∞ : Measure ℝ) = a • μ + b • ν) :
    μ = (nevLeaf h h0b h0 ∞ : Measure ℝ) := by
  refine nevLeaf_infinity_unique h h0b h0 hmom ?_
  have hzero := nevLeaf_infinity_carried h h0b h0
  rw [hmix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul] at hzero
  have hsum := (add_eq_zero.mp hzero).1
  rcases mul_eq_zero.mp hsum with hc | hc
  · exact absurd hc ha
  · exact hc

/-- **A half-half mixture equal to a leaf is trivial.**  The classical extremality statement. -/
theorem nevLeaf_of_half_mixture (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    (hν : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν)
    (hmix : (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = (1 / 2 : ENNReal) • μ + (1 / 2 : ENNReal) • ν) :
    μ = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) ∧
      ν = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := by
  have hhalf : (1 / 2 : ENNReal) ≠ 0 := by simp
  have hmix' : (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = (1 / 2 : ENNReal) • ν + (1 / 2 : ENNReal) • μ := by
    rw [hmix, add_comm]
  exact ⟨nevLeaf_eq_of_mixture h h0b h0 tau hμ hhalf hmix,
    nevLeaf_eq_of_mixture h h0b h0 tau hν hhalf hmix'⟩

end HTGeometry
