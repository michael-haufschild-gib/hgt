import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWSourcePhysicalCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursatTransposition

/-!
# Ordered literal-source Dirichlet transposition on finite null rectangles

The physical first-event source is extended by zero across the radial wall.
Its negative-time part already vanishes on the physical half-line.  Hence this
is exactly the original event-set indicator and is continuous.  The same test
can be transported in the direct chart based at `y` and the image chart based
at `-y`, without replacing the source by a separable or native surrogate.

The image chart retains its displaced physical wedge inside the test.  This
closes finite direct-minus-image assembly; noncompact limit and PW magnitude
remain separate proof burdens.
-/

open MeasureTheory Set

namespace RHTower.D4BMPWOrderedSourceFiniteDirichletTransposition

open GaloisForLFunctions.HTGeometry
open D4BMJointSource D4BMModularCore D4BMFullAngularGoursatTransposition
open D4BMGlobalAngularResponse D4BMFullAngularCircle D4BMFullAngularCircleAction
  D4BMCausalKernel D4BMNativeCircle

noncomputable section
set_option autoImplicit false

/-- Retained two-leg source in a chart based at `z`. For `z=y` it is direct;
for `z=-y` it is the reflected-image arm with the same physical source. -/
def orderedNullTest (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (s y z : ℝ) : ℝ × ℝ → ℂ :=
  fun p => physicalSourceCutoff (physicalRate q b) a
      (s - (p.1 + p.2) / 2, z + (p.1 - p.2) / 2) *
    timeReducedCoefficient (physicalRate q c) d s y

theorem orderedNullTest_continuous (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (s y z : ℝ) : Continuous (orderedNullTest q b c a d s y z) := by
  unfold orderedNullTest
  exact ((physicalSourceCutoff_continuous (physicalRate q b) a).comp (by fun_prop)).mul
    continuous_const

def finiteArm (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (s y z X k U V : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
    fullAngularRiemannKernel q branch ((u + v) / 2)
      (z + (u - v) / 2) z X k * orderedNullTest q b c a d s y z (u, v)

def finiteCap (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (s y z X k U V : ℝ) : ℂ :=
  fullAngularField q branch ![X, Real.exp k] *
    backwardRectanglePrimitive (orderedNullTest q b c a d s y z) U V (0, 0)

def finiteLift (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (s y z X k U V : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
    parameter q branch *
      (fullAngularRiemannKernel q branch ((u + v) / 2) (z + (u - v) / 2) z X k +
        D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
          (z + (u - v) / 2) z X k) /
      (4 * (Real.cosh (z + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
        backwardRectanglePrimitive (orderedNullTest q b c a d s y z) U V (u, v)

theorem finiteArm_eq_cap_add_lift (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (s y z X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    finiteArm q branch b c a d s y z X k U V =
      finiteCap q branch b c a d s y z X k U V +
        finiteLift q branch b c a d s y z X k U V := by
  unfold finiteArm finiteCap finiteLift
  exact fullAngularRiemannKernel_continuous_test_transposition q branch z X k U V hU hV
    (orderedNullTest q b c a d s y z)
    (orderedNullTest_continuous q b c a d s y z)

private theorem scalar_dirichlet_rearrange (A B C D : ℂ) :
    ((A + B) - (C + D)) / 4 = (A - C) / 4 + (B - D) / 4 := by
  ring

/-- Exact finite direct-minus-image incidence for the original physical
source. Both image and native forcing survive; no equality of caps is assumed. -/
theorem finite_dirichlet_source_transposition
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (s y X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (finiteArm q branch b c a d s y y X k U V -
      finiteArm q branch b c a d s y (-y) X k U V) / 4 =
    (finiteCap q branch b c a d s y y X k U V -
        finiteCap q branch b c a d s y (-y) X k U V) / 4 +
      (finiteLift q branch b c a d s y y X k U V -
        finiteLift q branch b c a d s y (-y) X k U V) / 4 := by
  rw [finiteArm_eq_cap_add_lift q branch b c a d s y y X k U V hU hV,
    finiteArm_eq_cap_add_lift q branch b c a d s y (-y) X k U V hU hV]
  exact scalar_dirichlet_rearrange _ _ _ _

end
end RHTower.D4BMPWOrderedSourceFiniteDirichletTransposition
