import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursatTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing

/-!
# Literal cyclic Peierls nonseparable transposition

The full two-event CTP density is not separable in Goursat null variables:
its two time legs retain their shared center time.  This file instantiates the
mixed-test full-kernel transposition with that exact source factor on every
finite null rectangle.

Proof-chain role:
`literal cyclic Peierls source -> nonseparable finite full-kernel transport
 -> ordered finite-part/lift-defect incidence -> residual cusp current -> PW-B`.
It transports the direct Riemann channel only; direct-minus-image assembly and
the noncompact ordered limit remain explicit later seams.
-/

open MeasureTheory Set

namespace RHTower.D4BMLiteralCyclicPeierlsNonseparableTransposition

open GaloisForLFunctions.HTGeometry
open D4BMCausalKernel D4BMFullAngularCircleAction D4BMGlobalAngularResponse D4BMHorizon
  D4BMJointSource D4BMModularCore D4BMNativeCircle D4BMFullAngularGoursatTransposition

noncomputable section
set_option autoImplicit false

/-- Exact two-leg CTP source factor after the direct Goursat coordinate change.
`s` is the retained center time, `y` is the second radial coordinate, and
neither can be removed without changing the source. -/
def literalCTPNullLeft (q : XiZeroCopy) (b : Bool) (a : ℂ) (s y : ℝ) : ℝ × ℝ → ℂ :=
  (fun z : ℝ × ℝ => timeReducedCoefficient (physicalRate q b) a z.1 z.2) ∘
    fun p : ℝ × ℝ => (s - (p.1 + p.2) / 4, y + (p.1 - p.2) / 2)

def literalCTPNullRight (q : XiZeroCopy) (c : Bool) (d : ℂ) (s y : ℝ) : ℝ × ℝ → ℂ :=
  (fun z : ℝ × ℝ => timeReducedCoefficient (physicalRate q c) d z.1 z.2) ∘
    fun p : ℝ × ℝ => (s + (p.1 + p.2) / 4, y)

def literalCTPNullTest (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (s y : ℝ) : ℝ × ℝ → ℂ :=
  literalCTPNullLeft q b a s y * literalCTPNullRight q c d s y

private theorem literalCTPNullLeft_continuous (q : XiZeroCopy) (b : Bool) (a : ℂ) (s y : ℝ) :
    Continuous (literalCTPNullLeft q b a s y) := by
  unfold literalCTPNullLeft
  apply (timeReducedCoefficient_joint_continuous (physicalRate q b) a).comp
  fun_prop

private theorem literalCTPNullRight_continuous (q : XiZeroCopy) (c : Bool) (d : ℂ) (s y : ℝ) :
    Continuous (literalCTPNullRight q c d s y) := by
  unfold literalCTPNullRight
  apply (timeReducedCoefficient_joint_continuous (physicalRate q c) d).comp
  fun_prop

/-- The literal CTP test is continuous in both null coordinates, but no
factorization assertion is made or used. -/
theorem literalCTPNullTest_continuous (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (s y : ℝ) :
    Continuous (literalCTPNullTest q b c a d s y) := by
  unfold literalCTPNullTest
  exact (literalCTPNullLeft_continuous q b a s y).mul
    (literalCTPNullRight_continuous q c d s y)

/-- Coordinate audit: this is the exact source factor in the direct CTP face.
The two source times are respectively `s-h/2` and `s+h/2` with
`h=(u+v)/2`; their common center `s` remains present. -/
theorem literalCTPNullTest_coordinate (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (s y u v : ℝ) :
    literalCTPNullTest q b c a d s y (u, v) =
      timeReducedCoefficient (physicalRate q b) a (s - (u + v) / 4) (y + (u - v) / 2) *
        timeReducedCoefficient (physicalRate q c) d (s + (u + v) / 4) y := rfl

/-- Finite direct-channel transposition of the literal, center-time-coupled
two-event CTP test.  The right side retains both full and native forcing
channels and evaluates the exact source through one two-face primitive. -/
theorem fullAngularRiemannKernel_literalCTPNull_transposition
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (s y X k U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2)
        (y + (u - v) / 2) y X k * literalCTPNullTest q b c a d s y (u, v)) =
      fullAngularField q branch ![X, Real.exp k] *
          backwardRectanglePrimitive (literalCTPNullTest q b c a d s y) U V (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2)
                (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              backwardRectanglePrimitive (literalCTPNullTest q b c a d s y) U V (u, v) :=
  fullAngularRiemannKernel_continuous_test_transposition q branch y X k U V hU hV
    (literalCTPNullTest q b c a d s y) (literalCTPNullTest_continuous q b c a d s y)

end

end RHTower.D4BMLiteralCyclicPeierlsNonseparableTransposition
