import GaloisForLFunctions.RHTower.DeningerKummerSpaceInner

/-!
# Positivity and additivity of the `L²` form on the Kummer space

The `L²` place norm is a sum of squares with positive weights, so it is nonnegative; the property
descends through the Kummer group to the Kummer space.  The form is additive in each argument on
the space, by the addition law of the divisible hull together with homogeneity.

* `deningerL2NormSq_nonneg` : the place norm is nonnegative.
* `deningerSpaceL2Inner_self_nonneg` : the form is positive semidefinite.
* `deningerSpaceL2Inner_add_left` : additivity on the Kummer space.
-/

namespace RHTower

open NumberField

open scoped IntermediateField

section Nonneg

variable {K : Type*} [Field K] [NumberField K]

/-- **The `L²` place norm is nonnegative.** -/
theorem deningerL2NormSq_nonneg (x : K) : 0 ≤ deningerL2NormSq x := by
  refine add_nonneg (Finset.sum_nonneg fun v _ => ?_) (finsum_nonneg fun w => ?_)
  · positivity
  · positivity

end Nonneg

section AbsoluteNonneg

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The absolute form is positive semidefinite.** -/
theorem deningerAbsL2Inner_self_nonneg {α : F} (hα : α ≠ 0) : 0 ≤ deningerAbsL2Inner α α := by
  have hαm : α ∈ (ℚ⟮α, α⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, α} (by simp)
  rw [deningerAbsL2Inner_intermediateField (ℚ⟮α, α⟯ : IntermediateField ℚ F) hαm hαm hα hα,
    deningerNormalizedL2Inner, deningerL2Inner_self]
  exact div_nonneg (deningerL2NormSq_nonneg _) (Nat.cast_nonneg _)

theorem deningerKummerL2Inner_self_nonneg (x : deningerKummerGroup F) :
    0 ≤ deningerKummerL2Inner x x := by
  induction x using QuotientGroup.induction_on with
  | H u => exact deningerAbsL2Inner_self_nonneg u.ne_zero

theorem deningerKummerAddL2Inner_self_nonneg (a : deningerKummerAdd F) :
    0 ≤ deningerKummerAddL2Inner a a :=
  deningerKummerL2Inner_self_nonneg _

/-- **The form on the Kummer space is positive semidefinite.** -/
theorem deningerSpaceL2Inner_self_nonneg (x : deningerKummerSpace F) :
    0 ≤ deningerSpaceL2Inner x x := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    rw [deningerSpaceL2Inner_mk]
    have hs : (0 : ℝ) < ((s : ℕ) : ℝ) := by exact_mod_cast s.pos
    exact div_nonneg (deningerKummerAddL2Inner_self_nonneg m) (by positivity)

end AbsoluteNonneg

section Additive

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

theorem deningerKummerAddL2Inner_add_left (a b c : deningerKummerAdd F) :
    deningerKummerAddL2Inner (a + b) c
      = deningerKummerAddL2Inner a c + deningerKummerAddL2Inner b c :=
  deningerKummerL2Inner_mul_left _ _ _

/-- **The form on the Kummer space is additive in the first argument.** -/
theorem deningerSpaceL2Inner_add_left (x y z : deningerKummerSpace F) :
    deningerSpaceL2Inner (x + y) z = deningerSpaceL2Inner x z + deningerSpaceL2Inner y z := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    induction y using DivisibleHull.ind with
    | mk n t =>
      induction z using DivisibleHull.ind with
      | mk p u =>
        have hs : (0 : ℝ) < ((s : ℕ) : ℝ) := by exact_mod_cast s.pos
        have ht : (0 : ℝ) < ((t : ℕ) : ℝ) := by exact_mod_cast t.pos
        have hu : (0 : ℝ) < ((u : ℕ) : ℝ) := by exact_mod_cast u.pos
        rw [DivisibleHull.mk_add_mk, deningerSpaceL2Inner_mk, deningerSpaceL2Inner_mk,
          deningerSpaceL2Inner_mk, deningerKummerAddL2Inner_add_left,
          deningerKummerAddL2Inner_nsmul_left, deningerKummerAddL2Inner_nsmul_left]
        have hst : ((((s * t : ℕ+)) : ℕ) : ℝ) = ((s : ℕ) : ℝ) * ((t : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hst]
        field_simp

/-- **The form on the Kummer space is additive in the second argument.** -/
theorem deningerSpaceL2Inner_add_right (x y z : deningerKummerSpace F) :
    deningerSpaceL2Inner x (y + z) = deningerSpaceL2Inner x y + deningerSpaceL2Inner x z := by
  rw [deningerSpaceL2Inner_comm, deningerSpaceL2Inner_add_left,
    deningerSpaceL2Inner_comm y x, deningerSpaceL2Inner_comm z x]

end Additive

end RHTower
