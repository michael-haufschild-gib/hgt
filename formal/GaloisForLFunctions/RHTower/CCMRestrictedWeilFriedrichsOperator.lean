import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator
import GaloisForLFunctions.RHTower.CCMArchimedeanDenseFormCore

/-!
# Canonical operator of the exact restricted CCM Weil form

The exact archimedean form domain embeds compactly, injectively, and densely into the physical
aperture.  The polar evaluations and every prime with `n ≤ exp (2a)` form one bounded
self-adjoint remainder.  Applying the bounded-perturbation Friedrichs construction therefore
produces the canonical lower-bounded self-adjoint operator of the restricted Weil form, with an
explicit compact resolvent.

Unlike an abstract packaging of a form assumption, every ingredient below is the literal source
term already constructed from the Riemann--Siegel phase, the two polar evaluation vectors, and the
finite von Mangoldt translation sum.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Exact restricted Weil sesquilinear form on the complete archimedean form domain. -/
def ccmRestrictedWeilForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v +
    inner ℂ
      (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a v)

/-- Uniform lower bound of the exact restricted Weil form. -/
theorem ccmRestrictedWeilForm_lowerBound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    -‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a u u).re := by
  have hBnorm :
      |(inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re| ≤
        ‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    calc
      |(inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re| ≤
          ‖inner ℂ
            (ccmRestrictedWeilBoundedRemainder a
              (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a u)‖ :=
        Complex.abs_re_le_norm _
      _ ≤
          ‖ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u)‖ *
            ‖ccmArchimedeanFormToAperture a u‖ :=
        norm_inner_le_norm _ _
      _ ≤
          (‖ccmRestrictedWeilBoundedRemainder a‖ *
            ‖ccmArchimedeanFormToAperture a u‖) *
              ‖ccmArchimedeanFormToAperture a u‖ :=
        mul_le_mul_of_nonneg_right
          ((ccmRestrictedWeilBoundedRemainder a).le_opNorm _)
          (norm_nonneg _)
      _ = ‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by ring
  unfold ccmRestrictedWeilForm
  rw [inner_self_eq_norm_sq_to_K]
  simp only [Complex.add_re, Complex.ofReal_re]
  have hbelow :
      -(‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2) ≤
        (inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re :=
    (neg_le_neg hBnorm).trans (neg_abs_le _)
  nlinarith [sq_nonneg ‖u‖]

/-- Canonical self-adjoint operator representing the exact restricted Weil form. -/
def ccmRestrictedWeilOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →ₗ.[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFriedrichsOperator
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)

/-- Connes--Consani's restricted Weil operator is self-adjoint, unconditionally. -/
theorem ccmRestrictedWeilOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmRestrictedWeilOperator a) := by
  exact boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)

/-- An explicit point of compact resolvent for the exact restricted Weil operator. -/
theorem ccmRestrictedWeilOperator_hasCompactResolventAt_negShift
    (a : SuzukiPositiveAperture) :
    LinearPMap.HasCompactResolventAt
      (ccmRestrictedWeilOperator a)
      (-(boundedPerturbedFormShift
        (ccmRestrictedWeilBoundedRemainder a) : ℂ)) := by
  exact boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    (isCompactOperator_ccmArchimedeanFormToAperture a)

/-- Exact first representation theorem for the source restricted Weil form. -/
theorem ccmRestrictedWeilOperator_represents_form
    (a : SuzukiPositiveAperture) (y : suzukiApertureHilbert a)
    (v : CCMArchimedeanFormDomain a) :
    let C := boundedPerturbedFormCovariance
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    let x : (ccmRestrictedWeilOperator a).domain :=
      ⟨C y, by
        change C y ∈ (closedDenseInverse C).domain
        exact (closedDenseInverse_apply_C C
          (boundedPerturbedFormCovariance_injective
            (ccmArchimedeanFormToAperture a)
            (ccmRestrictedWeilBoundedRemainder a)
            (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
            (ccmArchimedeanFormToAperture_injective a)
            (denseRange_ccmArchimedeanFormToAperture a)) y).1⟩
    let u := boundedPerturbedFormRieszInv
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
      ((ccmArchimedeanFormToAperture a).adjoint y)
    (x : suzukiApertureHilbert a) = ccmArchimedeanFormToAperture a u ∧
      inner ℂ (ccmRestrictedWeilOperator a x)
          (ccmArchimedeanFormToAperture a v) =
        ccmRestrictedWeilForm a u v := by
  exact boundedPerturbedFriedrichsOperator_represents_form
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    y v

end RHTower
