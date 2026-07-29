import GaloisForLFunctions.HTGeometry.BooleanEdgeFieldWitnesses

/-!
# Flatness of global actuality-wall coordinates

A globally defined family of Boolean event walls assigns each state one side of every wall.
Relative wall profiles are Boolean differences of those vertex coordinates.  They therefore form
an exact cocycle, have zero triangular holonomy, recover states exactly up to wall
indistinguishability, and induce a flat Boolean edge field on every graph of states.

This is a mathematical obstruction only: it does not identify physical events with walls or the
failure of a global wall system with gravity.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {X : Type u} {W : Type v}

/-- The Boolean profile of walls separating `point` from `base`. -/
def actualityWallProfile (side : W → X → Bool) (base point : X) : W → Bool :=
  fun w => Bool.xor (side w point) (side w base)

@[simp] theorem actualityWallProfile_apply (side : W → X → Bool)
    (base point : X) (w : W) :
    actualityWallProfile side base point w =
      Bool.xor (side w point) (side w base) := rfl

@[simp] theorem actualityWallProfile_self (side : W → X → Bool) (x : X) :
    actualityWallProfile side x x = fun _ => false := by
  funext w
  exact Bool.xor_self (side w x)

theorem actualityWallProfile_symm (side : W → X → Bool) (x y : X) :
    actualityWallProfile side x y = actualityWallProfile side y x := by
  funext w
  exact Bool.xor_comm (side w y) (side w x)

/-- Difference of two profiles with one basepoint is their direct relative profile. -/
theorem actualityWallProfile_difference (side : W → X → Bool) (base x y : X) :
    (fun w => Bool.xor
      (actualityWallProfile side base x w)
      (actualityWallProfile side base y w)) =
      actualityWallProfile side x y := by
  funext w
  simp only [actualityWallProfile]
  cases side w x <;> cases side w y <;> cases side w base <;> rfl

/-- Changing the actual basepoint translates every wall profile by one fixed profile. -/
theorem actualityWallProfile_changeBase (side : W → X → Bool) (base newBase x : X) :
    actualityWallProfile side newBase x =
      fun w => Bool.xor
        (actualityWallProfile side base x w)
        (actualityWallProfile side base newBase w) := by
  funext w
  simp only [actualityWallProfile]
  cases side w x <;> cases side w base <;> cases side w newBase <;> rfl

/-- Relative wall profiles form an exact Boolean cocycle. -/
theorem actualityWallProfile_cocycle (side : W → X → Bool) (a b c : X) :
    (fun w => Bool.xor
      (actualityWallProfile side a b w)
      (actualityWallProfile side b c w)) =
      actualityWallProfile side a c := by
  funext w
  simp only [actualityWallProfile]
  cases side w a <;> cases side w b <;> cases side w c <;> rfl

/-- Every triangular wall-profile holonomy is zero. -/
theorem actualityWallProfile_triangleHolonomy (side : W → X → Bool) (a b c : X) :
    (fun w => Bool.xor
      (Bool.xor
        (actualityWallProfile side a b w)
        (actualityWallProfile side b c w))
      (actualityWallProfile side c a w)) =
      fun _ => false := by
  funext w
  simp only [actualityWallProfile]
  cases side w a <;> cases side w b <;> cases side w c <;> rfl

/-- Two states are indistinguishable by all walls when every wall assigns them the same side. -/
def WallIndistinguishable (side : W → X → Bool) (x y : X) : Prop :=
  ∀ w, side w x = side w y

/-- A family of walls separates points when wall-indistinguishability is equality. -/
def WallsSeparatePoints (side : W → X → Bool) : Prop :=
  ∀ ⦃x y⦄, WallIndistinguishable side x y → x = y

theorem actualityWallProfile_eq_iff (side : W → X → Bool) (base x y : X) :
    actualityWallProfile side base x = actualityWallProfile side base y ↔
      WallIndistinguishable side x y := by
  constructor
  · intro h w
    have hw := congrFun h w
    cases hx : side w x <;>
      cases hy : side w y <;>
      cases hb : side w base <;>
      simp_all [actualityWallProfile]
  · intro h
    funext w
    simp only [actualityWallProfile]
    rw [h w]

/-- A relative wall profile is faithful exactly when the global wall family separates points. -/
theorem actualityWallProfile_injective_iff (side : W → X → Bool) (base : X) :
    Function.Injective (actualityWallProfile side base) ↔
      WallsSeparatePoints side := by
  constructor
  · intro hinj x y hxy
    apply hinj
    exact (actualityWallProfile_eq_iff side base x y).2 hxy
  · intro hsep x y hxy
    exact hsep ((actualityWallProfile_eq_iff side base x y).1 hxy)

/-- Every global wall coordinate is a Boolean vertex coboundary and hence has zero holonomy
on every closed walk, on every graph of states. -/
theorem globalActualityWallCoordinate_flat (G : SimpleGraph X)
    (side : W → X → Bool) (w : W) :
    BooleanEdgeFieldFlat G (fun x y => actualityWallProfile side x y w) := by
  exact booleanEdgeFieldFlat_of_coboundary
    (side w) (fun x y => actualityWallProfile side x y w) (by
      intro x y _
      simp only [actualityWallProfile]
      exact Bool.xor_comm _ _)

end GaloisForLFunctions.HTGeometry
