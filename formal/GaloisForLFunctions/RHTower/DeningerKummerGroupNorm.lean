import GaloisForLFunctions.RHTower.DeningerAbsoluteHeightSeminorm
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.GroupTheory.Torsion

/-!
# The Kummer group and its height norm

The absolute height is a group seminorm on the units of an algebraic extension of `ℚ`, and its
null set is exactly the torsion subgroup.  Dividing by the torsion therefore produces a group
carrying a genuine norm: the Kummer group `𝒢 = Q̄ˣ/μ_∞` with the Weil height as its norm.

* `deningerKummerSeminorm` : the seminorm on the units.
* `deningerKummerSeminorm_eq_zero_iff` : its null set is the torsion.
* `deningerKummerGroup` : the quotient by the torsion.
* `deningerKummerNorm` : the induced norm, positive definite off the identity.
-/

namespace RHTower

open NumberField

section KummerSeminorm

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

omit [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] in
/-- A unit has finite order exactly when its value does. -/
theorem deningerUnits_isOfFinOrder_iff {u : Fˣ} : IsOfFinOrder (u : F) ↔ IsOfFinOrder u := by
  simp only [isOfFinOrder_iff_pow_eq_one]
  refine exists_congr fun n => and_congr_right fun _ => ?_
  rw [← Units.val_pow_eq_pow_val, ← Units.val_one, Units.val_inj]

/-- **The height is a group seminorm on the units.** -/
noncomputable def deningerKummerSeminorm (F : Type*) [Field F] [Algebra ℚ F]
    [Algebra.IsAlgebraic ℚ F] : GroupSeminorm Fˣ where
  toFun u := deningerAbsHeight (u : F)
  map_one' := deningerAbsHeight_one
  mul_le' u v := deningerAbsHeight_mul_le (u : F) (v : F)
  inv' u := by
    show deningerAbsHeight ((u⁻¹ : Fˣ) : F) = deningerAbsHeight (u : F)
    rw [Units.val_inv_eq_inv_val, deningerAbsHeight_inv]

@[simp] theorem deningerKummerSeminorm_apply (u : Fˣ) :
    deningerKummerSeminorm F u = deningerAbsHeight (u : F) := rfl

/-- **The null set of the height seminorm is the torsion subgroup.** -/
theorem deningerKummerSeminorm_eq_zero_iff (u : Fˣ) :
    deningerKummerSeminorm F u = 0 ↔ u ∈ CommGroup.torsion Fˣ := by
  rw [deningerKummerSeminorm_apply, CommGroup.mem_torsion,
    deningerAbsHeight_eq_zero_iff (u.ne_zero), deningerUnits_isOfFinOrder_iff]

/-- The height is unchanged by multiplication by a torsion unit. -/
theorem deningerKummerSeminorm_mul_torsion {u t : Fˣ} (ht : t ∈ CommGroup.torsion Fˣ) :
    deningerKummerSeminorm F (u * t) = deningerKummerSeminorm F u := by
  have h0 : deningerKummerSeminorm F t = 0 := (deningerKummerSeminorm_eq_zero_iff t).mpr ht
  have hinv : deningerKummerSeminorm F t⁻¹ = 0 := by
    rw [map_inv_eq_map (deningerKummerSeminorm F) t, h0]
  refine le_antisymm ?_ ?_
  · have hle := map_mul_le_add (deningerKummerSeminorm F) u t
    rw [h0, add_zero] at hle
    exact hle
  · have hle := map_mul_le_add (deningerKummerSeminorm F) (u * t) t⁻¹
    rw [hinv, add_zero, mul_assoc, mul_inv_cancel, mul_one] at hle
    exact hle

end KummerSeminorm

section KummerGroup

variable (F : Type*) [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The Kummer group** `𝒢 = Fˣ/μ_∞`. -/
abbrev deningerKummerGroup : Type _ := Fˣ ⧸ CommGroup.torsion Fˣ

variable {F}

/-- The height descends to the Kummer group. -/
noncomputable def deningerKummerNormFun : deningerKummerGroup F → ℝ :=
  Quotient.lift (fun u => deningerKummerSeminorm F u) <| by
    intro a b hab
    have hmem : a⁻¹ * b ∈ CommGroup.torsion Fˣ := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, deningerKummerSeminorm_mul_torsion hmem]

@[simp] theorem deningerKummerNormFun_mk (u : Fˣ) :
    deningerKummerNormFun (QuotientGroup.mk u : deningerKummerGroup F)
      = deningerAbsHeight (u : F) := rfl

/-- **The height is a norm on the Kummer group.**  It is a seminorm because the height is
subadditive and inversion-invariant, and it is positive definite because its null set is exactly
the torsion that has been divided out. -/
noncomputable def deningerKummerNorm : GroupNorm (deningerKummerGroup F) where
  toFun := deningerKummerNormFun
  map_one' := deningerAbsHeight_one
  mul_le' := by
    refine Quotient.ind₂ fun a b => ?_
    exact map_mul_le_add (deningerKummerSeminorm F) a b
  inv' := by
    refine Quotient.ind fun a => ?_
    exact map_inv_eq_map (deningerKummerSeminorm F) a
  eq_one_of_map_eq_zero' := by
    refine Quotient.ind fun a ha => ?_
    exact (QuotientGroup.eq_one_iff a).mpr ((deningerKummerSeminorm_eq_zero_iff a).mp ha)

@[simp] theorem deningerKummerNorm_mk (u : Fˣ) :
    deningerKummerNorm (QuotientGroup.mk u : deningerKummerGroup F)
      = deningerAbsHeight (u : F) := rfl

end KummerGroup

end RHTower
