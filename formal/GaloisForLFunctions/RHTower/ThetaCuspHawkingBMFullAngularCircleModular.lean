import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeModularTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularJointJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCovectorHyperbolicEnergy

/-! Modular transport of the literal full angular circle response.

The HB-B2 base-jet tail must be estimated on the modular quotient, but only
after transporting the actual circle centered at the base point. This file
proves that transport for the constructed full response and its physical
center covector. It does not assert a growth bound, a cap interchange, or a
Peierls action.
-/

open UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff

namespace RHTower.D4BMFullAngularCircleModular

open D4BMHorizon D4BMModularCore D4BMNativeCircle
open D4BMFullAngularCircle D4BMFullAngularCircleJointJets
open D4BMFullCovectorHyperbolicEnergy

noncomputable section
set_option autoImplicit false

private theorem fullAngularField_coordinates (q : XiZeroCopy) (branch : Bool)
    (z : UpperHalfPlane) :
    fullAngularField q branch (coordinates z) = fullAngular q branch z := by
  change fullAngular q branch
    (ofComplex (angularCoordinates.symm (angularCoordinates (z : ℂ)))) =
      fullAngular q branch z
  rw [angularCoordinates.symm_apply_apply, ofComplex_apply]

private theorem fullAngularField_modular (q : XiZeroCopy) (branch : Bool)
    (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    fullAngularField q branch (coordinates (A • z)) =
      fullAngularField q branch (coordinates z) := by
  rw [fullAngularField_coordinates, fullAngularField_coordinates]
  simpa only [PSL2Z_mk_smul] using
    fullAngular_invariant q branch (QuotientGroup.mk A) z

private theorem circleAverage_fullAngular (q : XiZeroCopy) (branch : Bool)
    (d : ℝ) (z : UpperHalfPlane) :
    circleAverage (fun w => fullAngularField q branch (coordinates w)) d z =
      angularMean q branch d z.re (Real.log z.im) := by
  rw [circleAverage_coordinates]
  rfl

/-- The actual constructed full circle response is modular invariant in its
physical center, with its literal radius retained. -/
theorem angularMean_modular (q : XiZeroCopy) (branch : Bool) (d : ℝ)
    (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    angularMean q branch d (A • z).re (Real.log (A • z).im) =
      angularMean q branch d z.re (Real.log z.im) := by
  calc
    angularMean q branch d (A • z).re (Real.log (A • z).im) =
        circleAverage (fun w => fullAngularField q branch (coordinates w)) d (A • z) :=
      (circleAverage_fullAngular q branch d (A • z)).symm
    _ = circleAverage (fun w => fullAngularField q branch (coordinates w)) d z :=
      circleAverage_modular _ (fullAngularField_modular q branch) d A z
    _ = angularMean q branch d z.re (Real.log z.im) :=
      circleAverage_fullAngular q branch d z

/-- The literal full circle response in physical base coordinates. -/
def physicalMeanCovector (q : XiZeroCopy) (branch : Bool) (d : ℝ) : Covector :=
  coexact (physicalMean q branch d)

private theorem physicalMean_modular (q : XiZeroCopy) (branch : Bool) (d : ℝ)
    (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    physicalMean q branch d (coordinates (A • z)) =
      physicalMean q branch d (coordinates z) := by
  change angularMean q branch d (A • z).re (Real.log (A • z).im) =
    angularMean q branch d z.re (Real.log z.im)
  exact angularMean_modular q branch d A z

/-- The actual physical center covector of the full circle response transforms
with the literal modular Jacobian. -/
theorem physicalMeanCovector_modular (q : XiZeroCopy) (branch : Bool) (d : ℝ)
    (A : SL(2, ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (physicalMeanCovector q branch d) (coordinates (A • z))
      ((1 / denom A z ^ 2) * v) =
      covectorAction (physicalMeanCovector q branch d) (coordinates z) v := by
  unfold physicalMeanCovector
  exact coexact_modular_action A (physicalMean q branch d)
    (fun p hp => physicalMean_contDiffAt q branch d p hp)
    (physicalMean_modular q branch d A) z v

/-- Hyperbolic covector energy of the literal full circle response is exactly
modular invariant. -/
theorem physicalMeanCovector_hyperbolicEnergy_modular (q : XiZeroCopy)
    (branch : Bool) (d : ℝ) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    hyperbolicCovectorEnergy (physicalMeanCovector q branch d) (A • z) =
      hyperbolicCovectorEnergy (physicalMeanCovector q branch d) z :=
  hyperbolicCovectorEnergy_modular _ A z
    (physicalMeanCovector_modular q branch d A z)

end
end RHTower.D4BMFullAngularCircleModular
