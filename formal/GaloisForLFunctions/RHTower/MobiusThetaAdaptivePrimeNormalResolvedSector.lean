import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalCodiagonal
import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw

/-!
# Closed conservative resolved sector from the adaptive prime-normal source

The adaptive prime-normal source splits canonically into its labelled prime diagonal and its exact
post-prime arithmetic tail.  Retaining these two channels before codiagonalization gives a resolved
source map.  Its codiagonal is exactly the previously constructed adaptive source operator, whose
lower modulus is `3/4`.

This module proves that the resolved source range is closed and that its closure meets the universal
codiagonal kernel only at zero.  It therefore constructs the source-side strict sector demanded by
resolution-before-reduction, before any Hilbert consumer is applied.

No claim is made that the reflected-Gaussian completed Green antidiagonal belongs to this sector.
That cross-geometry arithmetic membership, which cannot be supplied by a bounded Hilbert
postcomparison, is the remaining selection theorem.
-/

open Complex Function Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Resolved adaptive source retaining labelled diagonal and exact arithmetic tail separately. -/
def adaptivePrimeNormalResolvedSource
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    AdaptivePrimeL1 →L[ℂ] (AdaptiveArithmeticL1 × AdaptiveArithmeticL1) :=
  (adaptivePrimeNormalDiagonalEmbedding.toContinuousLinearMap).prod
    (adaptivePrimeNormalTailOperator N w hNw)

@[simp]
theorem adaptivePrimeNormalResolvedSource_apply
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    adaptivePrimeNormalResolvedSource N w hNw x =
      (adaptivePrimeNormalDiagonalEmbedding x,
        adaptivePrimeNormalTailOperator N w hNw x) :=
  rfl

/-- Codiagonalization of the resolved source is the exact adaptive prime-normal source. -/
theorem resolvedDefectCodiagonal_adaptivePrimeNormalResolvedSource
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalResolvedSource N w hNw x) =
      adaptivePrimeNormalCodiagonal N w hNw x := by
  rfl

/-- The resolved codiagonal retains the quantitative `3/4` lower modulus. -/
theorem resolvedDefectCodiagonal_adaptivePrimeNormalResolvedSource_lower_bound
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    (3 / 4 : ℝ) * ‖x‖ ≤
      ‖resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalResolvedSource N w hNw x)‖ := by
  rw [resolvedDefectCodiagonal_adaptivePrimeNormalResolvedSource]
  exact adaptivePrimeNormalCodiagonal_lower_bound N w hNw x

/-- Source-side resolved arithmetic sector before Hilbertization. -/
def adaptivePrimeNormalResolvedSector
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    Submodule ℂ (AdaptiveArithmeticL1 × AdaptiveArithmeticL1) :=
  LinearMap.range (adaptivePrimeNormalResolvedSource N w hNw).toLinearMap

/-- The resolved source map has closed range already before using its codiagonal lower bound. -/
theorem adaptivePrimeNormalResolvedSource_isClosed_range
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    IsClosed (Set.range (adaptivePrimeNormalResolvedSource N w hNw)) := by
  have hanti :
      AntilipschitzWith 1 (adaptivePrimeNormalResolvedSource N w hNw) := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ (1 : ℝ) *
      ‖(adaptivePrimeNormalDiagonalEmbedding (x - y),
        adaptivePrimeNormalTailOperator N w hNw (x - y))‖
    rw [one_mul, Prod.norm_def,
      adaptivePrimeNormalDiagonalEmbedding.norm_map]
    exact le_max_left _ _
  exact hanti.isClosed_range
    (adaptivePrimeNormalResolvedSource N w hNw).uniformContinuous

theorem adaptivePrimeNormalResolvedSector_isClosed
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    IsClosed (adaptivePrimeNormalResolvedSector N w hNw :
      Set (AdaptiveArithmeticL1 × AdaptiveArithmeticL1)) := by
  change IsClosed (Set.range (adaptivePrimeNormalResolvedSource N w hNw))
  exact adaptivePrimeNormalResolvedSource_isClosed_range N w hNw

/-- Codiagonal augmentation is conservative on the resolved adaptive source sector. -/
theorem adaptivePrimeNormalResolvedSector_conservative :
    ∀ (N : ℕ) (w : ℂ)
      (hNw : (1 / 2 : ℝ) ≤
        (N : ℝ) * (mobiusThetaCenteredParameter w).re),
    IsConservativeOn
      (resolvedDefectCodiagonal (R := ℂ) (Z := AdaptiveArithmeticL1))
      (adaptivePrimeNormalResolvedSector N w hNw) := by
  intro N w hNw
  change Disjoint
    (adaptivePrimeNormalResolvedSector N w hNw)
    (LinearMap.ker
      (resolvedDefectCodiagonal (R := ℂ) (Z := AdaptiveArithmeticL1)))
  rw [Submodule.disjoint_def]
  intro z hzrange hzkernel
  obtain ⟨x, rfl⟩ := hzrange
  have hcx : adaptivePrimeNormalCodiagonal N w hNw x = 0 := by
    change resolvedDefectCodiagonal (R := ℂ)
      (adaptivePrimeNormalResolvedSource N w hNw x) = 0 at hzkernel
    rw [resolvedDefectCodiagonal_adaptivePrimeNormalResolvedSource] at hzkernel
    exact hzkernel
  have hx : x = 0 :=
    adaptivePrimeNormalCodiagonal_injective N w hNw
      (by simpa using hcx)
  subst x
  exact map_zero _

/-- Exact strictness statement: even after closure, the adaptive resolved sector has no nonzero
antidiagonal/codiagonal-null source. -/
theorem adaptivePrimeNormalResolvedSector_closure_inter_codiagonalKernel
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    closure (adaptivePrimeNormalResolvedSector N w hNw :
        Set (AdaptiveArithmeticL1 × AdaptiveArithmeticL1)) ∩
        (LinearMap.ker (resolvedDefectCodiagonal
          (R := ℂ) (Z := AdaptiveArithmeticL1)) :
          Set (AdaptiveArithmeticL1 × AdaptiveArithmeticL1)) =
      {0} := by
  rw [(adaptivePrimeNormalResolvedSector_isClosed N w hNw).closure_eq]
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, hkernel⟩
    have hcx : adaptivePrimeNormalCodiagonal N w hNw x = 0 := by
      change resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalResolvedSource N w hNw x) = 0 at hkernel
      rw [resolvedDefectCodiagonal_adaptivePrimeNormalResolvedSource] at hkernel
      exact hkernel
    have hx : x = 0 :=
      adaptivePrimeNormalCodiagonal_injective N w hNw
        (by simpa using hcx)
    subst x
    simp
  · rintro rfl
    constructor
    · exact ⟨0, map_zero _⟩
    · exact LinearMap.mem_ker.mpr (map_zero _)

end

end RHTower
