import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularCoexact

/-! The constructed response and both literal source covectors obey the actual modular tensor law. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem response_coordinates (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    fullAngularField q branch (coordinates z) = fullAngular q branch z := by
  change fullAngular q branch (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ)))) = _
  rw [angularCoordinates.symm_apply_apply,ofComplex_apply]

/-- The full response covector has the actual modular pullback law. -/
theorem fullAngularCovector_modular (q : XiZeroCopy) (branch : Bool) (A : SL(2,ℤ))
    (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (fullAngularCovector q branch) (coordinates (A • z)) ((1/(denom A z)^(2 : ℕ))*v) =
      covectorAction (fullAngularCovector q branch) (coordinates z) v := by
  apply coexact_modular_action A _ (fullAngularField_smooth q branch)
  intro w
  rw [response_coordinates,response_coordinates]
  simpa only [PSL2Z_mk_smul] using fullAngular_invariant q branch (QuotientGroup.mk A) w

/-- The complete half-square potential is an invariant scalar of the actual modular geometry. -/
theorem fullSquarePotential_modular (q : XiZeroCopy) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    fullSquarePotential q (coordinates (A • z)) = fullSquarePotential q (coordinates z) := by
  simp only [fullSquarePotential,xi_scalar_modular]

private theorem square_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fullSquarePotential q) z := by
  apply contDiffAt_infty.mpr
  intro n
  exact fullSquarePotential_smooth q z hz n

private theorem square_action (q : XiZeroCopy) (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (coexact (fullSquarePotential q)) (coordinates z) v =
      covectorAction (fullSquareCovector q) (coordinates z) v := by
  simp only [covectorAction,fullSquarePotential_coexact q (coordinates z) z.im_pos]

/-- The original quadratic source covector transforms with the actual modular Jacobian. -/
theorem fullSquareCovector_modular (q : XiZeroCopy) (A : SL(2,ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (fullSquareCovector q) (coordinates (A • z)) ((1/(denom A z)^(2 : ℕ))*v) =
      covectorAction (fullSquareCovector q) (coordinates z) v := by
  have h := coexact_modular_action A _ (square_smooth q) (fullSquarePotential_modular q A) z v
  simpa only [square_action] using h

/-- The full gradient-source scalar is modular invariant, retaining its differential origin. -/
theorem fullGradientEnergy_modular (q : XiZeroCopy) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    fullGradientEnergy q (coordinates (A • z)) = fullGradientEnergy q (coordinates z) := by
  have hd := chartLaplacian_modular_pullback A (fun w => fullSquarePotential q (coordinates w))
    (chartSmooth_coordinates _ (square_smooth q)) z
  have hi : (fun w : UpperHalfPlane => fullSquarePotential q (coordinates (A • w))) =
      (fun w : UpperHalfPlane => fullSquarePotential q (coordinates w)) :=
    funext (fullSquarePotential_modular q A)
  rw [hi,chartLaplacian_coordinates,chartLaplacian_coordinates] at hd
  have he := fullSquarePotential_laplacian q false (coordinates z) z.im_pos
  have heA := fullSquarePotential_laplacian q false (coordinates (A • z)) (A • z).im_pos
  rw [scalarLaplacian_eq _ _ z.im_pos] at he
  rw [scalarLaplacian_eq _ _ (A • z).im_pos,fullSquarePotential_modular] at heA
  dsimp only [hyperbolicLaplacian] at hd
  linear_combination he-heA-hd

/-- Every derivative of the literal gradient-source scalar exists at positive height. -/
theorem fullGradientEnergy_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fullGradientEnergy q) z := by
  have hs : ContDiffAt ℝ ∞ (scalar (center q)) z := by
    apply contDiffAt_infty.mpr
    intro n
    exact cuspLeg_contDiffAt .scalar (center q) n z hz
  have h0 : ContDiffAt ℝ ∞ (coordDeriv 0 (scalar (center q))) z := by
    apply coordDeriv_contDiffAt
    simpa using hs
  have h1 : ContDiffAt ℝ ∞ (coordDeriv 1 (scalar (center q))) z := by
    apply coordDeriv_contDiffAt
    simpa using hs
  have hy : ContDiffAt ℝ ∞ (fun w : Point => (w 1 : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  exact (hy.pow 2).mul ((h0.pow 2).add (h1.pow 2))

private theorem gradient_action (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (coexact (fullGradientEnergy q)) (coordinates z) v =
      2*covectorAction (fullGradientCovector q branch) (coordinates z) v := by
  simp only [covectorAction,fullGradientEnergy_coexact q branch (coordinates z) z.im_pos]
  ring

/-- The retained original gradient-source covector has the full modular tensor transformation law. -/
theorem fullGradientCovector_modular (q : XiZeroCopy) (branch : Bool) (A : SL(2,ℤ))
    (z : UpperHalfPlane) (v : ℂ) :
    covectorAction (fullGradientCovector q branch) (coordinates (A • z)) ((1/(denom A z)^(2 : ℕ))*v) =
      covectorAction (fullGradientCovector q branch) (coordinates z) v := by
  have h := coexact_modular_action A _ (fullGradientEnergy_smooth q) (fullGradientEnergy_modular q A) z v
  rw [gradient_action q branch,gradient_action q branch] at h
  linear_combination h/2

end
end RHTower.D4BMModularCore
