import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedIngoingCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamRadialFields
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-! Actual time/radial derivatives of the literal mixed current, with its
angular point held fixed during the orbit-coordinate differentiation. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMQuadraticMixedSource D4BMFundamentalScalarMetric D4BMScalarLinearEquation
set_option autoImplicit false
noncomputable section

/-- The original current field for one fixed angular point and component. -/
def orbitCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (x : Fin 4 → ℝ) : ℂ :=
  current (physicalRate q branch) (x 1) (envelope (physicalRate q branch) a x)
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)

private def angular0 (q : XiZeroCopy) (branch : Bool) (z : Point) (k : Fin 2) : ℂ :=
  let s := physicalRate q branch
  (5*s^2+15*s+4)/4*fullSquareCovector q k z

private def angular1 (q : XiZeroCopy) (branch : Bool) (z : Point) (k : Fin 2) : ℂ :=
  let s := physicalRate q branch
  s*(s-1)*(s+2)^2/4*fullSquareCovector q k z-
    s*(s-1)/4*fullGradientCovector q branch k z

private theorem expansion (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2) :
    orbitCurrent q branch a z k = fun x => envelope (currentRate q branch) (a^2) x *
      (angular0 q branch z k+((x 1 : ℂ)⁻¹*(x 1 : ℂ)⁻¹)*angular1 q branch z k) := by
  funext x
  rw [currentRate,envelope_double]
  simp only [orbitCurrent,current,angular0,angular1,div_eq_mul_inv,mul_inv_rev,pow_succ,pow_zero]
  ring

private theorem radius_smooth (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) x :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt

/-- The complete current orbit jet is the original currentJet, now identified
with actual coordinate derivatives of the original envelope. -/
theorem orbitCurrent_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (p : D4BMBackground.ExteriorPoint) :
    ofField (orbitCurrent q branch a z k) p.val =
      currentJet (physicalRate q branch) (p.val 1) (envelope (physicalRate q branch) a p.val)
        (fullSquareCovector q k z) (fullGradientCovector q branch k z) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hR := radius_smooth p.val
  have hU : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹) p.val := hR.inv hr
  have hP := (contDiffAt_const (c := angular0 q branch z k)).add
    ((hU.mul hU).mul (contDiffAt_const (c := angular1 q branch z k)))
  rw [expansion,ofField_mul (envelope_contDiffAt _ _ p 2) hP,
    ofField_add contDiffAt_const ((hU.mul hU).mul contDiffAt_const),ofField_constant,
    ofField_mul (hU.mul hU) contDiffAt_const,ofField_constant,ofField_mul hU hU,
    ofField_inv hR hr,coordinate_jet,envelope_jet,currentRate,envelope_double]
  rfl

/-- The original current field has the differentiability needed for a physical
onset product rule; angular data remain fixed and unmodified. -/
theorem orbitCurrent_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (p : D4BMBackground.ExteriorPoint) : ContDiffAt ℝ 2 (orbitCurrent q branch a z k) p.val := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hU : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹) p.val := (radius_smooth p.val).inv hr
  rw [expansion]
  exact (envelope_contDiffAt _ _ p 2).mul (contDiffAt_const.add ((hU.mul hU).mul contDiffAt_const))

/-- Both original orbit derivatives, with no independent jet-slot premise. -/
theorem orbitCurrent_derivatives (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (p : D4BMBackground.ExteriorPoint) :
    coordDeriv 0 (orbitCurrent q branch a z k) p.val = currentRate q branch*orbitCurrent q branch a z k p.val ∧
    coordDeriv 1 (orbitCurrent q branch a z k) p.val =
      currentFirst (physicalRate q branch) (p.val 1) (envelope (physicalRate q branch) a p.val)
        (fullSquareCovector q k z) (fullGradientCovector q branch k z) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^2-1 ≠ 0)
  have h := currentJet_components (physicalRate q branch) (p.val 1)
    (envelope (physicalRate q branch) a p.val) (fullSquareCovector q k z) (fullGradientCovector q branch k z) hr hf
  rw [← orbitCurrent_jet q branch a z k p] at h
  exact ⟨h.2.1,h.2.2⟩

end
end RHTower.D4BMModularCore
