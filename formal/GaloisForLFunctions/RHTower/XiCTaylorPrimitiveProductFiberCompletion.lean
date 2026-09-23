import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayGlobalReassembly
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge

/-!
# Primitive/product-fibre completion law

Two exact global decompositions of the finite theta-tail core current meet here.

* `XiCTaylorThetaTailProductFiberFiniteCoreGlobalBridge` regroups the completion-scaled current by
  multiplicative product fibre and leaves the core current together with one exact radial
  norm-square term.
* `XiCTaylorThetaTailPrimitiveRayGlobalReassembly` regroups the same core current by coprime
  direction into the joint reflected radial seam packets.

Substituting the second into the first eliminates the intermediate core current and expresses the
completion-scaled product-fibre sum directly in coprime-direction seam data.  No new convergence
or interchange is used: both source theorems already carry their own absolute convergence.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-- **Primitive/product-fibre completion law.**  The global sum of completion-scaled
product-fibre currents is four times the squared radial scale times the complete
coprime-direction reflected seam sum, minus the single exact completion norm-square term. -/
theorem tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq_primitiveDirection
    (d : ℕ) (z : ℂ) :
    (∑' k : ℕ,
      xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z k) =
      4 * Complex.normSq z ^ (2 : ℕ) *
          (∑' q : ThetaCuspPrimitiveDirection,
            ∫ r : ℝ in Ici
                (thetaCuspPrimitiveRayRadialLog (q.1.1 : ℕ) (q.1.2 : ℕ) 0 0),
              (8 * Real.exp
                (-(Real.log (q.1.1 : ℝ) + Real.log (q.1.2 : ℝ)) / 2)) *
              thetaCuspPrimitiveRayJointSeamIntegrand d z r
                (-Real.log (q.1.1 : ℝ)) (-Real.log (q.1.2 : ℝ))) -
        32 * Complex.normSq z * z.im *
          Complex.normSq ((xiCTaylorThetaTailCorePolynomial d).eval z) := by
  rw [tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq d z,
    xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionGlobalJoint d z]
  ring

end

end RHTower
