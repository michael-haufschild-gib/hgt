import GaloisForLFunctions.HTGeometry.ReversibleSnapshotIndependence
import Mathlib.Data.Fintype.Card

/-!
# Boolean-coordinate and quarter-event fairness

Toggling one Boolean coordinate pairs its true and false fibers. Combining this exact half-count
with a second conditional half-count yields the quarter guarantee used in the two-sided
game-of-Googol analysis.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- Toggling one coordinate pairs states where that bit is true with states where it is false. -/
def toggleTrueFalseEquiv (e : α) :
    {state : α → Bool // state e = true} ≃ {state : α → Bool // state e = false} where
  toFun state := ⟨toggleCoordinate e state, by simp [state.property]⟩
  invFun state := ⟨toggleCoordinate e state, by simp [state.property]⟩
  left_inv state := by
    apply Subtype.ext
    exact toggleCoordinate_involutive e state
  right_inv state := by
    apply Subtype.ext
    exact toggleCoordinate_involutive e state

/-- One Boolean coordinate is true on exactly half of all finite states. -/
theorem two_mul_card_state_eq_true [Fintype α] (e : α) :
    2 * Fintype.card {state : α → Bool // state e = true} =
      Fintype.card (α → Bool) := by
  let p : (α → Bool) → Prop := fun state => state e = true
  have htoggle :
      Fintype.card {state : α → Bool // state e = true} =
        Fintype.card {state : α → Bool // state e = false} :=
    Fintype.card_congr (toggleTrueFalseEquiv e)
  have hfalseNot :
      Fintype.card {state : α → Bool // state e = false} =
        Fintype.card {state : α → Bool // ¬p state} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by
      intro state
      change state e = false ↔ ¬state e = true
      cases state e <;> simp)
  have hrest :
      Fintype.card (α → Bool) -
          Fintype.card {state : α → Bool // p state} =
        Fintype.card {state : α → Bool // p state} := by
    rw [← Fintype.card_subtype_compl p, ← hfalseNot, ← htoggle]
  calc
    2 * Fintype.card {state : α → Bool // state e = true} =
        Fintype.card {state : α → Bool // p state} +
          Fintype.card {state : α → Bool // p state} := by
            simp [p, two_mul]
    _ = Fintype.card {state : α → Bool // p state} +
          (Fintype.card (α → Bool) -
            Fintype.card {state : α → Bool // p state}) :=
      congrArg _ hrest.symm
    _ = Fintype.card (α → Bool) :=
      Nat.add_sub_of_le (Fintype.card_subtype_le p)

/-- Two nested half-events occupy one quarter of a finite ambient space. -/
theorem four_mul_card_eq_of_two_halves
    {X : Type*} [Fintype X] [DecidableEq X] (outer inner : Finset X)
    (houter : 2 * outer.card = Fintype.card X)
    (hinner : 2 * (inner ∩ outer).card = outer.card) :
    4 * (inner ∩ outer).card = Fintype.card X := by
  calc
    4 * (inner ∩ outer).card = 2 * (2 * (inner ∩ outer).card) := by
      change (2 * 2) * (inner ∩ outer).card = 2 * (2 * (inner ∩ outer).card)
      exact Nat.mul_assoc 2 2 _
    _ = 2 * outer.card := congrArg (2 * ·) hinner
    _ = Fintype.card X := houter

/-- Lower-bound form: an event holding on at least half of a half-space has ambient mass at least
one quarter. -/
theorem card_le_four_mul_card_of_two_half_bounds
    {X : Type*} [Fintype X] [DecidableEq X] (outer inner : Finset X)
    (houter : 2 * outer.card = Fintype.card X)
    (hinner : outer.card ≤ 2 * (inner ∩ outer).card) :
    Fintype.card X ≤ 4 * (inner ∩ outer).card := by
  calc
    Fintype.card X = 2 * outer.card := houter.symm
    _ ≤ 2 * (2 * (inner ∩ outer).card) := Nat.mul_le_mul_left 2 hinner
    _ = 4 * (inner ∩ outer).card := by
      change 2 * (2 * (inner ∩ outer).card) = (2 * 2) * (inner ∩ outer).card
      exact (Nat.mul_assoc 2 2 _).symm

/-- Three nested exact half-events occupy one eighth of a finite ambient space. -/
theorem eight_mul_card_eq_of_three_halves
    {X : Type*} [Fintype X] [DecidableEq X]
    (outer middle inner : Finset X)
    (houter : 2 * outer.card = Fintype.card X)
    (hmiddle : 2 * (middle ∩ outer).card = outer.card)
    (hinner : 2 * (inner ∩ (middle ∩ outer)).card = (middle ∩ outer).card) :
    8 * (inner ∩ (middle ∩ outer)).card = Fintype.card X := by
  calc
    8 * (inner ∩ (middle ∩ outer)).card =
        2 * (2 * (2 * (inner ∩ (middle ∩ outer)).card)) := by
      change (2 * 2 * 2) * (inner ∩ (middle ∩ outer)).card =
        2 * (2 * (2 * (inner ∩ (middle ∩ outer)).card))
      simp only [Nat.mul_assoc]
    _ = 2 * (2 * (middle ∩ outer).card) := congrArg (fun n => 2 * (2 * n)) hinner
    _ = 2 * outer.card := congrArg (2 * ·) hmiddle
    _ = Fintype.card X := houter

/-- Lower-bound form of the three-half argument underlying the adversarial-order `1/8` factor. -/
theorem card_le_eight_mul_card_of_three_half_bounds
    {X : Type*} [Fintype X] [DecidableEq X]
    (outer middle inner : Finset X)
    (houter : 2 * outer.card = Fintype.card X)
    (hmiddle : outer.card ≤ 2 * (middle ∩ outer).card)
    (hinner : (middle ∩ outer).card ≤
      2 * (inner ∩ (middle ∩ outer)).card) :
    Fintype.card X ≤ 8 * (inner ∩ (middle ∩ outer)).card := by
  calc
    Fintype.card X = 2 * outer.card := houter.symm
    _ ≤ 2 * (2 * (middle ∩ outer).card) := Nat.mul_le_mul_left 2 hmiddle
    _ ≤ 2 * (2 * (2 * (inner ∩ (middle ∩ outer)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hinner)
    _ = 8 * (inner ∩ (middle ∩ outer)).card := by
      change 2 * (2 * (2 * (inner ∩ (middle ∩ outer)).card)) =
        (2 * 2 * 2) * (inner ∩ (middle ∩ outer)).card
      simp only [Nat.mul_assoc]

end GaloisForLFunctions.HTGeometry
