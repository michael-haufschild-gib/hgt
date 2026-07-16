import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.LinearRecurrenceStateSpace

/-!
# Strict Hankel geometry of a reciprocal observation tail

The canonical algebraic tail `r n = 1/(n+1)` is the moment sequence of Lebesgue measure restricted
to `[0,1]`.  The representing measure has infinite support, so every finite Hankel block of `r` is
strictly positive definite and has positive determinant.  Hence the tail escapes every fixed finite
modal, spectral, or linear state-space description, even locally on arbitrarily long finite windows.

The positive content is the continuum observation representation, not merely the finite-model
no-go.  The index can label clock readings, detector samples, or arithmetic observations; no
evolution equation is assumed.
-/

open Set MeasureTheory

namespace HTGeometry

noncomputable section

/-- The canonical reciprocal algebraic observation tail. -/
def reciprocalTailClock (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- The continuum palette representing the reciprocal tail. -/
def reciprocalTailMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

/-- The reciprocal tail is exactly the moment sequence of the unit interval. -/
theorem reciprocalTailClock_eq_moment (n : ℕ) :
    reciprocalTailClock n = ∫ x, x ^ n ∂reciprocalTailMeasure := by
  change 1 / ((n : ℝ) + 1) = ∫ x in Icc (0 : ℝ) 1, x ^ n
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

/-- All moments are integrable against the compact continuum palette. -/
theorem reciprocalTailMeasure_integrable_moments (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) reciprocalTailMeasure := by
  change IntegrableOn (fun x : ℝ ↦ x ^ n) (Icc 0 1)
  exact (continuous_id.pow n).integrableOn_Icc

/-- Removing finitely many report values leaves positive mass in the continuum palette. -/
theorem reciprocalTailMeasure_infiniteSupport (F : Finset ℝ) :
    0 < reciprocalTailMeasure {x : ℝ | x ∉ F} := by
  have hFzero : volume (↑F : Set ℝ) = 0 :=
    F.finite_toSet.measure_zero volume
  rw [reciprocalTailMeasure]
  change 0 < (volume.restrict (Icc 0 1)) ((↑F : Set ℝ)ᶜ)
  rw [Measure.restrict_apply F.measurableSet.compl]
  have hset : (↑F : Set ℝ)ᶜ ∩ Icc 0 1 = Icc 0 1 \ (↑F : Set ℝ) := by
    ext x
    simp [and_comm]
  rw [hset, measure_diff_null hFzero]
  norm_num

/-- **All-order strict Hankel law.**  Every finite reciprocal-tail Hankel determinant is positive. -/
theorem det_momentHankelMatrix_reciprocalTailClock_pos (n : ℕ) :
    0 < (momentHankelMatrix reciprocalTailClock n).det :=
  det_momentHankelMatrix_pos_of_infiniteSupport reciprocalTailClock
    reciprocalTailClock_eq_moment reciprocalTailMeasure_integrable_moments
    reciprocalTailMeasure_infiniteSupport n

/-- The reciprocal tail has no finite modal presentation of any prescribed width. -/
theorem reciprocalTailClock_not_finiteModalWidthAtMost (d : ℕ) :
    ¬ FiniteModalWidthAtMost d reciprocalTailClock := by
  apply not_finiteModalWidthAtMost_of_det_ne_zero
  simpa [algebraicHankelMatrix, momentHankelMatrix] using
    ne_of_gt (det_momentHankelMatrix_reciprocalTailClock_pos (d + 1))

/-- The reciprocal continuum clock satisfies no positive finite-order linear recurrence. -/
theorem reciprocalTailClock_not_linearRecurrence
    (E : LinearRecurrence ℝ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution reciprocalTailClock := by
  intro hsolution
  have hzero := det_algebraicHankelMatrix_succ_eq_zero_of_linearRecurrence
    E hsolution horder
  have hpositive := det_momentHankelMatrix_reciprocalTailClock_pos (E.order + 1)
  exact (ne_of_gt hpositive) (by
    simpa [algebraicHankelMatrix, momentHankelMatrix] using hzero)

/-- No uniformly bounded finite spectral palette can reproduce arbitrarily long reciprocal-tail
windows, even when the approximating palette may change with the window. -/
theorem reciprocalTailClock_not_fixedSpectralWidthLocalClosure (d : ℕ) :
    ¬ FixedSpectralWidthLocalClosure d reciprocalTailClock :=
  not_fixedSpectralWidthLocalClosure_of_infiniteSupport
    reciprocalTailClock_eq_moment reciprocalTailMeasure_integrable_moments
    reciprocalTailMeasure_infiniteSupport

/-- No uniformly bounded linear hidden-state model can reproduce arbitrarily long reciprocal-tail
windows, even when its realization may change with the window. -/
theorem reciprocalTailClock_not_fixedStateSpaceDimensionLocalClosure (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d reciprocalTailClock :=
  not_fixedStateSpaceDimensionLocalClosure_of_infiniteSupport
    reciprocalTailClock_eq_moment reciprocalTailMeasure_integrable_moments
    reciprocalTailMeasure_infiniteSupport

end

end HTGeometry
