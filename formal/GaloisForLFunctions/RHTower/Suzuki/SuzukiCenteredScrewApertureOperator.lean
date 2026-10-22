import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureL2Equivalence
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilBoundedRemainder

/-!
# Suzuki's centered screw operator on the physical aperture

The trace-class interval operator with kernel

`g(t-u) - g(t) - g(-u) + g(0)`

is transported through the exact interval/zero-extension unitary.  The resulting bounded operator
acts on the same physical aperture Hilbert space as the restricted Weil Friedrichs operator.
Everything remains literal: the pairing theorem below recovers Suzuki's double integral, and
self-adjointness is proved by unitary transport of the source kernel symmetry.
-/

open Complex
open scoped InnerProduct

noncomputable section

namespace RHTower

def suzukiApertureL2EquivCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] suzukiApertureHilbert a :=
  (suzukiApertureL2Equiv a).toContinuousLinearEquiv.toContinuousLinearMap

def suzukiApertureL2EquivSymmCLM (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiApertureL2Equiv a).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Suzuki's centered screw-kernel operator, on the physical zero-extended aperture space. -/
def suzukiCenteredScrewApertureOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  suzukiApertureL2EquivCLM a ∘L
    suzukiScrewIntegralOperator a.1 ∘L suzukiApertureL2EquivSymmCLM a

theorem suzukiCenteredScrewApertureOperator_apply
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    suzukiCenteredScrewApertureOperator a f =
      suzukiApertureL2Equiv a
        (suzukiScrewIntegralOperator a.1 ((suzukiApertureL2Equiv a).symm f)) := by
  rfl

/-- Exact source pairing after transport to the physical aperture. -/
theorem inner_suzukiCenteredScrewApertureOperator_eq_intervalForm
    (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a) :
    inner ℂ g (suzukiCenteredScrewApertureOperator a f) =
      suzukiScrewIntervalForm a.1
        ((suzukiApertureL2Equiv a).symm f)
        ((suzukiApertureL2Equiv a).symm g) := by
  rw [suzukiCenteredScrewApertureOperator_apply]
  let e := suzukiApertureL2Equiv a
  calc
    inner ℂ g (e (suzukiScrewIntegralOperator a.1 (e.symm f))) =
        inner ℂ (e (e.symm g))
          (e (suzukiScrewIntegralOperator a.1 (e.symm f))) := by
      rw [e.apply_symm_apply]
    _ = inner ℂ (e.symm g) (suzukiScrewIntegralOperator a.1 (e.symm f)) :=
      e.inner_map_map _ _
    _ = suzukiScrewIntervalForm a.1 (e.symm f) (e.symm g) :=
      inner_suzukiScrewIntegralOperator_eq_intervalForm_pair a.2.le _ _

/-- Unconditional self-adjointness of Suzuki's centered screw operator. -/
theorem suzukiCenteredScrewApertureOperator_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiCenteredScrewApertureOperator a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change inner ℂ (suzukiCenteredScrewApertureOperator a f) g =
    inner ℂ f (suzukiCenteredScrewApertureOperator a g)
  rw [suzukiCenteredScrewApertureOperator_apply,
    suzukiCenteredScrewApertureOperator_apply]
  let e := suzukiApertureL2Equiv a
  calc
    inner ℂ (e (suzukiScrewIntegralOperator a.1 (e.symm f))) g =
        inner ℂ (e (suzukiScrewIntegralOperator a.1 (e.symm f)))
          (e (e.symm g)) := by rw [e.apply_symm_apply]
    _ = inner ℂ (suzukiScrewIntegralOperator a.1 (e.symm f)) (e.symm g) :=
      e.inner_map_map _ _
    _ = inner ℂ (e.symm f) (suzukiScrewIntegralOperator a.1 (e.symm g)) :=
      suzukiScrewIntegralOperator_isSymmetric a.2.le (e.symm f) (e.symm g)
    _ = inner ℂ (e (e.symm f))
        (e (suzukiScrewIntegralOperator a.1 (e.symm g))) :=
      (e.inner_map_map _ _).symm
    _ = inner ℂ f (e (suzukiScrewIntegralOperator a.1 (e.symm g))) := by
      rw [e.apply_symm_apply]

end RHTower

