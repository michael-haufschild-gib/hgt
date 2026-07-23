import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayGlobalReassembly
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge

/-!
# Primitive-direction reassembly of the completed product-fibre current

The finite-core current has two exact arithmetic presentations: completion first regroups it by
positive product fibres, while the uncompleted current reassembles it by complete coprime radial
directions.  Their common current term gives an exact formula joining both decompositions.  The
only term not carried by primitive directions is the radial norm-square created by completion.
-/

open Complex Real MeasureTheory Set Polynomial

namespace RHTower

noncomputable section

/-- **Primitive/product-fibre completion law.**  The full completion-scaled product-fibre current
is the coprime-direction reflected radial seam sum at coefficient `4‖z‖⁴`, together with one exact
negative radial value term.  Completion creates no additional arithmetic seam. -/
theorem tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq_primitiveDirectionGlobalJoint
    (d : ℕ) (z : ℂ) :
    (∑' k : ℕ,
      xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z k) =
      4 * Complex.normSq z ^ 2 *
          (∑' q : ThetaCuspPrimitiveDirection,
            ∫ r : ℝ in Ici
                (thetaCuspPrimitiveRayRadialLog
                  (q.1.1 : ℕ) (q.1.2 : ℕ) 0 0),
              (8 * Real.exp
                (-(Real.log (q.1.1 : ℝ) + Real.log (q.1.2 : ℝ)) / 2)) *
              thetaCuspPrimitiveRayJointSeamIntegrand d z r
                (-Real.log (q.1.1 : ℝ)) (-Real.log (q.1.2 : ℝ))) -
        32 * Complex.normSq z * z.im *
          Complex.normSq ((xiCTaylorThetaTailCorePolynomial d).eval z) := by
  rw [tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq,
    xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionGlobalJoint]
  ring

end

end RHTower
