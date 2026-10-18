import GaloisForLFunctions.RHTower.CHMDQuotientWeilForm
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity

/-!
# Actual SZ, RW and CHMD coordinates on their common source core

The literal inverse-Doob lift maps Suzuki sources into the signed-radical quotient.
Its full Weil energy equals both the native restricted form and the screw-operator
quadratic form. No identification of their different completion norms is asserted.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower
noncomputable section
namespace RHTower
open CHMDDoobGraph

/-- The literal inverse-Doob source coordinate in the actual signed-radical quotient. -/
def suzukiCoreSignedQuotient (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) : SignedQuotient :=
  signedQuotientMk (testLift u (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport)

/-- All pole terms are retained in this unconditional actual-source identification. -/
theorem suzukiCoreSignedQuotient_weil (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    quotientWeilForm (suzukiCoreSignedQuotient a u) =
      (ccmRestrictedWeilForm a (suzukiRestrictedWeilCoreCCMFormVector a u)
        (suzukiRestrictedWeilCoreCCMFormVector a u)).re := by
  rw [suzukiCoreSignedQuotient, quotientWeilForm_testLift]
  have h := ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil
    (ccmComplexSmoothInteriorSourceOfRealCore a u)
  rw [ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector,
    ← ccmRestrictedWeilForm_self_re_eq_source] at h
  exact h.symm

theorem suzukiCoreSignedQuotient_restrictedWeil (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    quotientWeilForm (suzukiCoreSignedQuotient a u) = suzukiRestrictedWeilForm a.1 u u := by
  rw [suzukiCoreSignedQuotient_weil,
    ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm, ofReal_re]

/-- SZ screw, RW closed form and CHMD quotient agree on their actual common source core. -/
theorem suzukiCoreSignedQuotient_screw (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    quotientWeilForm (suzukiCoreSignedQuotient a u) =
      (inner ℂ (suzukiRestrictedWeilCoreDerivativeZeroMean a u)
        (suzukiScrewZeroMeanOperator a (suzukiRestrictedWeilCoreDerivativeZeroMean a u))).re := by
  rw [suzukiCoreSignedQuotient_weil,
    inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_ccmRestrictedWeilForm]

end RHTower

end
