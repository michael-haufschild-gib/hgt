import GaloisForLFunctions.RHTower.DeningerL2Space
import Mathlib.Analysis.InnerProductSpace.OfNorm

/-!
# The Hilbert--Kummer space is an inner product space

The `L²` norm on the Kummer space satisfies the parallelogram identity, because it comes from a
bilinear form.  This is the scalar-free hypothesis of the Fréchet--von Neumann--Jordan theorem, so
the space is inner-product-able.

* `deningerL2NormSpace_parallelogram` : the parallelogram identity for the `L²` norm.
* `deningerL2Space_innerProductSpaceable` : the Kummer space satisfies the scalar-free
  inner-product predicate.
-/

namespace RHTower

open NumberField

section Parallelogram

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The parallelogram identity for the `L²` norm, on the underlying Kummer space. -/
theorem deningerL2NormSpace_parallelogram (x y : deningerKummerSpace F) :
    deningerL2Norm (x + y) * deningerL2Norm (x + y)
        + deningerL2Norm (x - y) * deningerL2Norm (x - y)
      = 2 * (deningerL2Norm x * deningerL2Norm x + deningerL2Norm y * deningerL2Norm y) := by
  have hsq : ∀ z : deningerKummerSpace F,
      deningerL2Norm z * deningerL2Norm z = deningerSpaceL2Inner z z := by
    intro z
    rw [deningerL2Norm, Real.mul_self_sqrt (deningerSpaceL2Inner_self_nonneg _)]
  have hadd : deningerSpaceL2Inner (x + y) (x + y)
      = deningerSpaceL2Inner x x + 2 * deningerSpaceL2Inner x y
        + deningerSpaceL2Inner y y := by
    rw [deningerSpaceL2Inner_add_left, deningerSpaceL2Inner_add_right,
      deningerSpaceL2Inner_add_right, deningerSpaceL2Inner_comm y x]
    ring
  have hsub : deningerSpaceL2Inner (x - y) (x - y)
      = deningerSpaceL2Inner x x - 2 * deningerSpaceL2Inner x y
        + deningerSpaceL2Inner y y := by
    rw [sub_eq_add_neg, deningerSpaceL2Inner_add_left, deningerSpaceL2Inner_add_right,
      deningerSpaceL2Inner_add_right, deningerSpaceL2Inner_neg_left,
      deningerSpaceL2Inner_comm x (-y), deningerSpaceL2Inner_neg_left,
      deningerSpaceL2Inner_comm y x, deningerSpaceL2Inner_neg_neg]
    ring
  rw [hsq, hsq, hsq, hsq, hadd, hsub]
  ring

/-- **The parallelogram identity on the Kummer space.** -/
theorem deningerL2Norm_parallelogram (x y : DeningerL2Space F) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
  deningerL2NormSpace_parallelogram (F := F) x y

/-- **The Kummer space is inner-product-able**: its `L²` norm satisfies the parallelogram
identity, which is the scalar-free form of coming from an inner product. -/
instance deningerL2Space_innerProductSpaceable :
    InnerProductSpaceable (DeningerL2Space F) :=
  ⟨deningerL2Norm_parallelogram⟩

end Parallelogram

end RHTower
