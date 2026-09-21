import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialOverlap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquareNormalForm

/-!
# Physical self-copy inverse-square noncancellation for cyclic Peierls

This leaf transports the closed literal normal-form no-go to the actual
fundamental QNM frequency.  It does not impose a radial normalization: the
coefficient is the `overlapInverseSquare` retained by the actual mixed radial
current.

Proof-chain role:
`literal cyclic Peierls B2 residual -> physical self-copy inverse-square
coefficient is nonzero -> no radial-constant cap face cancels every literal
radial fibre -> RBH/PW B2 obstruction or coefficientwise extinction`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsSelfInverseSquarePhysical

open Set
open D4BMModularCore D4BMJointSource D4BMMixedRadialOverlap
open D4BMLiteralCyclicPeierlsSelfInverseSquareNormalForm

noncomputable section
set_option autoImplicit false

/-- The literal self-copy inverse-square coefficient is exactly the physical
mixed-current coefficient after the fundamental QNM is restored. -/
theorem self_overlapInverseSquare_eq_normalForm (q : XiZeroCopy)
    (branch side : Bool) :
    overlapInverseSquare (physicalRate q branch)
      (physicalFundamentalFrequency q side) =
        selfInverseSquareFactor q branch side := by
  rw [physicalFundamentalFrequency_eq]
  rfl

/-- No physical self-copy source arm can lose its inverse-square mixed-current
coefficient.  This is the radial term which a B2 cap/contact equality would
have to cancel coefficientwise. -/
theorem self_overlapInverseSquare_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    overlapInverseSquare (physicalRate q branch)
      (physicalFundamentalFrequency q side) ≠ 0 := by
  rw [self_overlapInverseSquare_eq_normalForm]
  exact selfInverseSquareFactor_ne_zero q branch side

/-- Physical radial affine coefficient after any cap contribution whose
coefficient is constant on a radial fibre. -/
def physicalAffineResidual (q : XiZeroCopy) (branch side : Bool) (A K : ℂ)
    (r : Ioi (1 : ℝ)) : ℂ :=
  (A + overlapInverseSquare (physicalRate q branch)
    (physicalFundamentalFrequency q side) / (r.val : ℂ) ^ 2) / 2 - K

/-- A radial-constant cap contribution cannot cancel the literal physical
self-copy inverse-square residual on every exterior fibre.  The witness is
unconditional and remains in the original radial coordinate. -/
theorem exists_physicalAffineResidual_ne_zero (q : XiZeroCopy)
    (branch side : Bool) (A K : ℂ) :
    ∃ r : Ioi (1 : ℝ), physicalAffineResidual q branch side A K r ≠ 0 := by
  rw [show physicalAffineResidual q branch side A K =
    affineResidual q branch side A K by
      funext r
      rw [self_overlapInverseSquare_eq_normalForm]
      rfl]
  exact exists_affineResidual_ne_zero q branch side A K

end
end RHTower.D4BMLiteralCyclicPeierlsSelfInverseSquarePhysical
