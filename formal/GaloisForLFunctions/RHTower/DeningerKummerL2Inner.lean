import GaloisForLFunctions.RHTower.DeningerAbsL2InnerAdditive
import GaloisForLFunctions.RHTower.DeningerKummerGroupNorm

/-!
# The `L²` inner product on the Kummer group

On the units of an algebraic extension of `ℚ` the absolute `L²` inner product is symmetric,
biadditive and zero whenever either argument is a root of unity.  It therefore descends to the
Kummer group `𝒢 = Q̄ˣ/μ_∞`.

* `deningerUnitL2Inner` : the form on the units.
* `deningerUnitL2Inner_mul_torsion_left` : invariance under a torsion factor.
* `deningerKummerL2Inner` : the descended form on `𝒢`.
-/

namespace RHTower

open NumberField

section UnitInner

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The absolute `L²` inner product on the units. -/
noncomputable def deningerUnitL2Inner (u v : Fˣ) : ℝ :=
  deningerAbsL2Inner (u : F) (v : F)

theorem deningerUnitL2Inner_comm (u v : Fˣ) :
    deningerUnitL2Inner u v = deningerUnitL2Inner v u :=
  deningerAbsL2Inner_comm u.ne_zero v.ne_zero

theorem deningerUnitL2Inner_mul_left (u u' v : Fˣ) :
    deningerUnitL2Inner (u * u') v = deningerUnitL2Inner u v + deningerUnitL2Inner u' v := by
  show deningerAbsL2Inner ((u : F) * (u' : F)) (v : F) = _
  exact deningerAbsL2Inner_mul_left u.ne_zero u'.ne_zero v.ne_zero

/-- **The form vanishes on torsion units.** -/
theorem deningerUnitL2Inner_torsion_left {t : Fˣ} (ht : t ∈ CommGroup.torsion Fˣ) (v : Fˣ) :
    deningerUnitL2Inner t v = 0 :=
  deningerAbsL2Inner_torsion_left t.ne_zero v.ne_zero
    (deningerUnits_isOfFinOrder_iff.mpr ((CommGroup.mem_torsion t).mp ht))

/-- **The form is unchanged by a torsion factor.** -/
theorem deningerUnitL2Inner_mul_torsion_left {u t : Fˣ} (ht : t ∈ CommGroup.torsion Fˣ) (v : Fˣ) :
    deningerUnitL2Inner (u * t) v = deningerUnitL2Inner u v := by
  rw [deningerUnitL2Inner_mul_left, deningerUnitL2Inner_torsion_left ht, add_zero]

/-- **The form is unchanged by a torsion factor in the second argument.** -/
theorem deningerUnitL2Inner_mul_torsion_right {v t : Fˣ} (ht : t ∈ CommGroup.torsion Fˣ)
    (u : Fˣ) : deningerUnitL2Inner u (v * t) = deningerUnitL2Inner u v := by
  rw [deningerUnitL2Inner_comm, deningerUnitL2Inner_mul_torsion_left ht,
    deningerUnitL2Inner_comm]

end UnitInner

section KummerInner

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The `L²` inner product on the Kummer group.** -/
noncomputable def deningerKummerL2Inner :
    deningerKummerGroup F → deningerKummerGroup F → ℝ :=
  Quotient.lift₂ (fun u v => deningerUnitL2Inner u v) <| by
    intro a b a' b' ha hb
    have hamem : a⁻¹ * a' ∈ CommGroup.torsion Fˣ := QuotientGroup.leftRel_apply.mp ha
    have hbmem : b⁻¹ * b' ∈ CommGroup.torsion Fˣ := QuotientGroup.leftRel_apply.mp hb
    have ha' : a' = a * (a⁻¹ * a') := by group
    have hb' : b' = b * (b⁻¹ * b') := by group
    rw [ha', hb', deningerUnitL2Inner_mul_torsion_left hamem,
      deningerUnitL2Inner_mul_torsion_right hbmem]

@[simp] theorem deningerKummerL2Inner_mk (u v : Fˣ) :
    deningerKummerL2Inner (QuotientGroup.mk u : deningerKummerGroup F) (QuotientGroup.mk v)
      = deningerAbsL2Inner (u : F) (v : F) := rfl

theorem deningerKummerL2Inner_comm (x y : deningerKummerGroup F) :
    deningerKummerL2Inner x y = deningerKummerL2Inner y x := by
  refine Quotient.ind₂ (fun a b => ?_) x y
  exact deningerUnitL2Inner_comm a b

theorem deningerKummerL2Inner_mul_left (x x' y : deningerKummerGroup F) :
    deningerKummerL2Inner (x * x') y
      = deningerKummerL2Inner x y + deningerKummerL2Inner x' y := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction x' using QuotientGroup.induction_on with
    | H a' =>
      induction y using QuotientGroup.induction_on with
      | H b => exact deningerUnitL2Inner_mul_left a a' b

theorem deningerKummerL2Inner_mul_right (x y y' : deningerKummerGroup F) :
    deningerKummerL2Inner x (y * y')
      = deningerKummerL2Inner x y + deningerKummerL2Inner x y' := by
  rw [deningerKummerL2Inner_comm, deningerKummerL2Inner_mul_left,
    deningerKummerL2Inner_comm y x, deningerKummerL2Inner_comm y' x]

end KummerInner

end RHTower
