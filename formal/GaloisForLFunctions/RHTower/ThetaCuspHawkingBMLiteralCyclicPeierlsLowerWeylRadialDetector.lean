import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence

/-!
# Physical lower-Weyl radial detector for literal cyclic Peierls

The lower physical reader Weyl coefficient and the literal self-copy
inverse-square radial coefficient are both nonzero to the left of the critical
line.  Consequently no radial-constant cap contribution can cancel their
product on both literal exterior fibres `R = 2, 3`.

Proof-chain role:
`left Xi copy -> nonzero lower reader Weyl channel and inverse-square overlap
-> two-fibre B2 residual detector -> causal cap/contact transport ->
RBH/PW-B/FZZ-P extinction -> RH`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsLowerWeylRadialDetector

open Set
open D4BMModularCore D4BMJointSource D4BMMixedRadialOverlap
open D4BMLiteralCyclicPeierlsAffineCuspIncidence
open D4BMLiteralCyclicPeierlsSelfInverseSquarePhysical

noncomputable section
set_option autoImplicit false

/-- The normalized lower Weyl residual on one exterior radial fibre.  `A`
absorbs every cap contribution whose coefficient is constant on that fibre. -/
def lowerWeylRadialDetector (q : XiZeroCopy) (branch side : Bool) (A : ℂ)
    (r : Ioi (1 : ℝ)) : ℂ :=
  A + lowerWeylFaceCoefficient q *
    overlapInverseSquare (physicalRate q branch)
      (physicalFundamentalFrequency q side) / (r.val : ℂ) ^ 2

private theorem lowerWeylFaceCoefficient_ne_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    lowerWeylFaceCoefficient q ≠ 0 := by
  intro h
  obtain hLambda := (lowerWeylFaceCoefficient_eq_zero_iff q).mp h
  exact affine_lower_lambda_zero_not_left q ⟨hLambda, hleft⟩

/-- The lower physical Weyl channel cannot be cancelled by a radial-constant
cap contribution on both literal witness fibres. -/
theorem lowerWeylRadialDetector_two_or_three_ne_zero (q : XiZeroCopy)
    (branch side : Bool) (A : ℂ) (hleft : (q.1 : ℂ).re < 1 / 2) :
    lowerWeylRadialDetector q branch side A ⟨2, by norm_num⟩ ≠ 0 ∨
      lowerWeylRadialDetector q branch side A ⟨3, by norm_num⟩ ≠ 0 := by
  by_contra h
  push Not at h
  have h2 := h.1
  have h3 := h.2
  have hL := lowerWeylFaceCoefficient_ne_zero q hleft
  have hI := self_overlapInverseSquare_ne_zero q branch side
  have hLI : lowerWeylFaceCoefficient q *
      overlapInverseSquare (physicalRate q branch)
        (physicalFundamentalFrequency q side) ≠ 0 :=
    mul_ne_zero hL hI
  have hzero : (5 : ℂ) * (lowerWeylFaceCoefficient q *
      overlapInverseSquare (physicalRate q branch)
        (physicalFundamentalFrequency q side)) = 0 := by
    unfold lowerWeylRadialDetector at h2 h3
    norm_num at h2 h3
    linear_combination 36 * h2 - 36 * h3
  exact hLI ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

end
end RHTower.D4BMLiteralCyclicPeierlsLowerWeylRadialDetector
