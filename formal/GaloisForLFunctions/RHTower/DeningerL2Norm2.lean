import GaloisForLFunctions.RHTower.DeningerL2CauchySchwarz

/-!
# The `L²` norm on the Kummer space

The square root of the diagonal of the `L²` form is a norm: the triangle inequality is
Cauchy--Schwarz, and definiteness is definiteness of the form.

* `deningerL2Norm` : the `L²` norm on `𝒢 ⊗ ℚ`.
* `deningerL2Norm_triangle` : the triangle inequality.
* `deningerL2AddGroupNorm` : the bundled norm.
-/

namespace RHTower

open NumberField

section L2Norm

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

theorem deningerSpaceL2Inner_zero_left (y : deningerKummerSpace F) :
    deningerSpaceL2Inner 0 y = 0 := by
  have h := deningerSpaceL2Inner_add_left 0 0 y
  rw [add_zero] at h
  linarith

theorem deningerSpaceL2Inner_neg_left (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner (-x) y = -deningerSpaceL2Inner x y := by
  have h := deningerSpaceL2Inner_add_left x (-x) y
  rw [add_neg_cancel, deningerSpaceL2Inner_zero_left] at h
  linarith

theorem deningerSpaceL2Inner_neg_neg (x : deningerKummerSpace F) :
    deningerSpaceL2Inner (-x) (-x) = deningerSpaceL2Inner x x := by
  rw [deningerSpaceL2Inner_neg_left, deningerSpaceL2Inner_comm x (-x),
    deningerSpaceL2Inner_neg_left, deningerSpaceL2Inner_comm x x]
  ring

/-- **The `L²` norm on the Kummer space.** -/
noncomputable def deningerL2Norm (x : deningerKummerSpace F) : ℝ :=
  Real.sqrt (deningerSpaceL2Inner x x)

theorem deningerL2Norm_nonneg (x : deningerKummerSpace F) : 0 ≤ deningerL2Norm x :=
  Real.sqrt_nonneg _

@[simp] theorem deningerL2Norm_zero : deningerL2Norm (0 : deningerKummerSpace F) = 0 := by
  rw [deningerL2Norm, deningerSpaceL2Inner_zero_left, Real.sqrt_zero]

theorem deningerL2Norm_neg (x : deningerKummerSpace F) :
    deningerL2Norm (-x) = deningerL2Norm x := by
  rw [deningerL2Norm, deningerL2Norm, deningerSpaceL2Inner_neg_neg]

/-- **Cauchy--Schwarz in norm form.** -/
theorem deningerSpaceL2Inner_le_norm (x y : deningerKummerSpace F) :
    deningerSpaceL2Inner x y ≤ deningerL2Norm x * deningerL2Norm y := by
  have h1 := deningerSpaceL2_cauchySchwarz x y
  have hxx := deningerSpaceL2Inner_self_nonneg x
  have h2 : deningerSpaceL2Inner x y
      ≤ Real.sqrt (deningerSpaceL2Inner x x * deningerSpaceL2Inner y y) := by
    rcases le_or_gt (deningerSpaceL2Inner x y) 0 with h | h
    · exact h.trans (Real.sqrt_nonneg _)
    · calc deningerSpaceL2Inner x y
          = Real.sqrt (deningerSpaceL2Inner x y * deningerSpaceL2Inner x y) :=
            (Real.sqrt_mul_self h.le).symm
        _ ≤ Real.sqrt (deningerSpaceL2Inner x x * deningerSpaceL2Inner y y) :=
            Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_mul hxx] at h2

/-- **The triangle inequality.** -/
theorem deningerL2Norm_triangle (x y : deningerKummerSpace F) :
    deningerL2Norm (x + y) ≤ deningerL2Norm x + deningerL2Norm y := by
  have hxx := deningerSpaceL2Inner_self_nonneg x
  have hyy := deningerSpaceL2Inner_self_nonneg y
  have hcs := deningerSpaceL2Inner_le_norm x y
  rw [deningerL2Norm, deningerL2Norm] at hcs
  have hexp : deningerSpaceL2Inner (x + y) (x + y)
      = deningerSpaceL2Inner x x + 2 * deningerSpaceL2Inner x y
        + deningerSpaceL2Inner y y := by
    rw [deningerSpaceL2Inner_add_left, deningerSpaceL2Inner_add_right,
      deningerSpaceL2Inner_add_right, deningerSpaceL2Inner_comm y x]
    ring
  have hbound : deningerSpaceL2Inner (x + y) (x + y)
      ≤ (deningerL2Norm x + deningerL2Norm y) ^ 2 := by
    rw [hexp, add_sq, deningerL2Norm, deningerL2Norm, Real.sq_sqrt hxx, Real.sq_sqrt hyy]
    nlinarith [hcs]
  calc deningerL2Norm (x + y) ≤ Real.sqrt ((deningerL2Norm x + deningerL2Norm y) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = deningerL2Norm x + deningerL2Norm y :=
        Real.sqrt_sq (add_nonneg (deningerL2Norm_nonneg x) (deningerL2Norm_nonneg y))

theorem deningerL2Norm_eq_zero {x : deningerKummerSpace F} (h : deningerL2Norm x = 0) :
    x = 0 := by
  refine deningerSpaceL2Inner_self_eq_zero ?_
  have hnn := deningerSpaceL2Inner_self_nonneg x
  have := (Real.sqrt_eq_zero hnn).mp h
  exact this

/-- **The bundled `L²` norm.** -/
noncomputable def deningerL2AddGroupNorm : AddGroupNorm (deningerKummerSpace F) where
  toFun := deningerL2Norm
  map_zero' := deningerL2Norm_zero
  add_le' := deningerL2Norm_triangle
  neg' := deningerL2Norm_neg
  eq_zero_of_map_eq_zero' _ := deningerL2Norm_eq_zero

end L2Norm

end RHTower
