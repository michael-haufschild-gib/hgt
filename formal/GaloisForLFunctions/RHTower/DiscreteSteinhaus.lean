/-
# Discrete Steinhaus / Hex crossing duality (general marking)

The full digital Jordan-curve separation on a rectangular board `Fin (m+1) × Fin (n+1)`:
for an *arbitrary* two-colouring `Mk`, either the marked cells contain a king (`8`-connected)
chain from the bottom row to the top row, or the free cells contain a rook (`4`-connected) chain
from the left column to the right column.  This drops the column-determined hypothesis of
`RHTower.discrete_crossing_duality_of_columnDetermined` and closes the crossing dichotomy for every
marking.

## Mechanism — the interface walk (Gale)

The board is padded with a frame of sentinel cells (marked bottom/top rows, free left/right columns)
against a neutral exterior.  A *directed interface edge* (`Dart`) is a lattice corner together with a
heading, carrying a **free** cell on its left and a **marked** cell on its right.  The successor rule
turns by reading the two cells ahead of the head vertex: marked-ahead-left turns left, free-then-marked
goes straight, free-then-free turns right.  The king/rook asymmetry enters at the single ambiguous
diagonal (ahead-left marked, ahead-right free): the walk keeps the two diagonally-marked cells on the
same shore, i.e. the marked king-shore wins the corner.

`succ` preserves the free-left/marked-right invariant (`good_succ`) and is invertible (`pred_succ`);
a start dart wedged in the sentinel corner has no predecessor.  Following the walk, the marked cells to
the right stay king-connected (`markShore_step`) and the free cells to the left stay rook-connected
(`freeShore_step`).  Finiteness of the frame forces the walk to leave the interior; the exit corner
reads off which colour crosses, and the interior of that monochromatic sentinel chain is the crossing
of the original board.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RectangleCrossingDuality

namespace RHTower

open Relation

namespace SteinhausWalk

/-- The three colours of the padded board: `marked` (king shore), `free` (rook shore) and the
`neutral` exterior beyond the sentinel frame. -/
inductive Color | marked | free | neutral
deriving DecidableEq, Repr

/-- The four headings of a directed interface edge. -/
inductive Dir | E | N | W | S
deriving DecidableEq, Repr

/-- Unit step vector of a heading. -/
def Dir.vec : Dir → ℤ × ℤ
  | .E => (1, 0) | .N => (0, 1) | .W => (-1, 0) | .S => (0, -1)

/-- Rotate a heading a quarter turn left (counter-clockwise). -/
def Dir.ccw : Dir → Dir
  | .E => .N | .N => .W | .W => .S | .S => .E

/-- Rotate a heading a quarter turn right (clockwise). -/
def Dir.cw : Dir → Dir
  | .E => .S | .S => .W | .W => .N | .N => .E

/-- A directed interface edge: the lattice corner `(x, y)` together with a heading `d`.  The edge is
the unit crack from `(x, y)` to `(x, y) + d.vec`. -/
structure Dart where
  x : ℤ
  y : ℤ
  d : Dir
deriving DecidableEq, Repr

/-- The cell on the left of the crack (free shore under the invariant). -/
def Dart.leftCell (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x, t.y) | .N => (t.x - 1, t.y) | .W => (t.x - 1, t.y - 1) | .S => (t.x, t.y - 1)

/-- The cell on the right of the crack (marked shore under the invariant). -/
def Dart.rightCell (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x, t.y - 1) | .N => (t.x, t.y) | .W => (t.x - 1, t.y) | .S => (t.x - 1, t.y - 1)

/-- The cell ahead and to the left of the head vertex. -/
def Dart.aheadLeft (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x + 1, t.y) | .N => (t.x - 1, t.y + 1) | .W => (t.x - 2, t.y - 1) | .S => (t.x, t.y - 2)

/-- The cell ahead and to the right of the head vertex. -/
def Dart.aheadRight (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x + 1, t.y - 1) | .N => (t.x, t.y + 1) | .W => (t.x - 2, t.y) | .S => (t.x - 1, t.y - 2)

section Board

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- The padded three-colour board.  Real cells `[0,m] × [0,n]` carry `Mk`; the frame adds a marked
bottom row (`j = -1`) and top row (`j = n+1`), free left column (`i = -1`, including the corner
`(-1,-1)`) and free right column (`i = m+1`); everything else is the neutral exterior. -/
def clr (c : ℤ × ℤ) : Color :=
  let i := c.1; let j := c.2
  if i = -1 ∧ (-1 ≤ j ∧ j ≤ (n : ℤ)) then Color.free
  else if i = (m : ℤ) + 1 ∧ (0 ≤ j ∧ j ≤ (n : ℤ)) then Color.free
  else if (0 ≤ i ∧ i ≤ (m : ℤ)) ∧ j = -1 then Color.marked
  else if (0 ≤ i ∧ i ≤ (m : ℤ)) ∧ j = (n : ℤ) + 1 then Color.marked
  else if h : (0 ≤ i ∧ i ≤ (m : ℤ)) ∧ (0 ≤ j ∧ j ≤ (n : ℤ)) then
    (if Mk (⟨i.toNat, by omega⟩, ⟨j.toNat, by omega⟩) then Color.marked else Color.free)
  else Color.neutral

/-- The free-left / marked-right orientation invariant. -/
def Good (t : Dart) : Prop := clr Mk t.leftCell = Color.free ∧ clr Mk t.rightCell = Color.marked

/-- The head vertex is at the frame boundary: continuing the walk would read a neutral exterior cell.
Where this fails the successor rule is well defined. -/
def Exits (t : Dart) : Prop :=
  clr Mk t.aheadLeft = Color.neutral ∨ clr Mk t.aheadRight = Color.neutral

/-- The successor interface edge.  Reads the two cells ahead: marked ahead-left turns left; free
ahead-left with marked ahead-right goes straight; free/free turns right.  (At an exit the ahead cells
are neutral and the value is a harmless default.) -/
def succ (t : Dart) : Dart :=
  if clr Mk t.aheadLeft = Color.marked then ⟨t.x + t.d.vec.1, t.y + t.d.vec.2, t.d.ccw⟩
  else if clr Mk t.aheadRight = Color.marked then ⟨t.x + t.d.vec.1, t.y + t.d.vec.2, t.d⟩
  else ⟨t.x + t.d.vec.1, t.y + t.d.vec.2, t.d.cw⟩

/-- The cell behind and to the left of the tail vertex (used to invert the walk). -/
def Dart.behindLeft (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x - 1, t.y) | .N => (t.x - 1, t.y - 1) | .W => (t.x, t.y - 1) | .S => (t.x, t.y)

/-- The cell behind and to the right of the tail vertex (used to invert the walk). -/
def Dart.behindRight (t : Dart) : ℤ × ℤ :=
  match t.d with
  | .E => (t.x - 1, t.y - 1) | .N => (t.x, t.y - 1) | .W => (t.x, t.y) | .S => (t.x - 1, t.y)

/-- The predecessor interface edge, the mirror of `succ`: reads the two cells behind the tail vertex,
turning clockwise where `succ` turns counter-clockwise. -/
def pred (t : Dart) : Dart :=
  if clr Mk t.behindLeft = Color.marked then
    ⟨t.x - t.d.cw.vec.1, t.y - t.d.cw.vec.2, t.d.cw⟩
  else if clr Mk t.behindRight = Color.marked then
    ⟨t.x - t.d.vec.1, t.y - t.d.vec.2, t.d⟩
  else
    ⟨t.x - t.d.ccw.vec.1, t.y - t.d.ccw.vec.2, t.d.ccw⟩

end Board

/-! Concrete-direction reduction lemmas: every dart-cell accessor evaluated on an explicit
heading, as `rfl`-simp-lemmas, so that arithmetic tactics see plain integer pairs. -/

@[simp] lemma vec_E : Dir.vec Dir.E = (1, 0) := rfl
@[simp] lemma vec_N : Dir.vec Dir.N = (0, 1) := rfl
@[simp] lemma vec_W : Dir.vec Dir.W = (-1, 0) := rfl
@[simp] lemma vec_S : Dir.vec Dir.S = (0, -1) := rfl
@[simp] lemma ccw_E : Dir.ccw Dir.E = Dir.N := rfl
@[simp] lemma ccw_N : Dir.ccw Dir.N = Dir.W := rfl
@[simp] lemma ccw_W : Dir.ccw Dir.W = Dir.S := rfl
@[simp] lemma ccw_S : Dir.ccw Dir.S = Dir.E := rfl
@[simp] lemma cw_E : Dir.cw Dir.E = Dir.S := rfl
@[simp] lemma cw_N : Dir.cw Dir.N = Dir.E := rfl
@[simp] lemma cw_W : Dir.cw Dir.W = Dir.N := rfl
@[simp] lemma cw_S : Dir.cw Dir.S = Dir.W := rfl

@[simp] lemma leftCell_E (x y : ℤ) : Dart.leftCell ⟨x, y, Dir.E⟩ = (x, y) := rfl
@[simp] lemma leftCell_N (x y : ℤ) : Dart.leftCell ⟨x, y, Dir.N⟩ = (x - 1, y) := rfl
@[simp] lemma leftCell_W (x y : ℤ) : Dart.leftCell ⟨x, y, Dir.W⟩ = (x - 1, y - 1) := rfl
@[simp] lemma leftCell_S (x y : ℤ) : Dart.leftCell ⟨x, y, Dir.S⟩ = (x, y - 1) := rfl
@[simp] lemma rightCell_E (x y : ℤ) : Dart.rightCell ⟨x, y, Dir.E⟩ = (x, y - 1) := rfl
@[simp] lemma rightCell_N (x y : ℤ) : Dart.rightCell ⟨x, y, Dir.N⟩ = (x, y) := rfl
@[simp] lemma rightCell_W (x y : ℤ) : Dart.rightCell ⟨x, y, Dir.W⟩ = (x - 1, y) := rfl
@[simp] lemma rightCell_S (x y : ℤ) : Dart.rightCell ⟨x, y, Dir.S⟩ = (x - 1, y - 1) := rfl
@[simp] lemma aheadLeft_E (x y : ℤ) : Dart.aheadLeft ⟨x, y, Dir.E⟩ = (x + 1, y) := rfl
@[simp] lemma aheadLeft_N (x y : ℤ) : Dart.aheadLeft ⟨x, y, Dir.N⟩ = (x - 1, y + 1) := rfl
@[simp] lemma aheadLeft_W (x y : ℤ) : Dart.aheadLeft ⟨x, y, Dir.W⟩ = (x - 2, y - 1) := rfl
@[simp] lemma aheadLeft_S (x y : ℤ) : Dart.aheadLeft ⟨x, y, Dir.S⟩ = (x, y - 2) := rfl
@[simp] lemma aheadRight_E (x y : ℤ) : Dart.aheadRight ⟨x, y, Dir.E⟩ = (x + 1, y - 1) := rfl
@[simp] lemma aheadRight_N (x y : ℤ) : Dart.aheadRight ⟨x, y, Dir.N⟩ = (x, y + 1) := rfl
@[simp] lemma aheadRight_W (x y : ℤ) : Dart.aheadRight ⟨x, y, Dir.W⟩ = (x - 2, y) := rfl
@[simp] lemma aheadRight_S (x y : ℤ) : Dart.aheadRight ⟨x, y, Dir.S⟩ = (x - 1, y - 2) := rfl
@[simp] lemma behindLeft_E (x y : ℤ) : Dart.behindLeft ⟨x, y, Dir.E⟩ = (x - 1, y) := rfl
@[simp] lemma behindLeft_N (x y : ℤ) : Dart.behindLeft ⟨x, y, Dir.N⟩ = (x - 1, y - 1) := rfl
@[simp] lemma behindLeft_W (x y : ℤ) : Dart.behindLeft ⟨x, y, Dir.W⟩ = (x, y - 1) := rfl
@[simp] lemma behindLeft_S (x y : ℤ) : Dart.behindLeft ⟨x, y, Dir.S⟩ = (x, y) := rfl
@[simp] lemma behindRight_E (x y : ℤ) : Dart.behindRight ⟨x, y, Dir.E⟩ = (x - 1, y - 1) := rfl
@[simp] lemma behindRight_N (x y : ℤ) : Dart.behindRight ⟨x, y, Dir.N⟩ = (x, y - 1) := rfl
@[simp] lemma behindRight_W (x y : ℤ) : Dart.behindRight ⟨x, y, Dir.W⟩ = (x, y) := rfl
@[simp] lemma behindRight_S (x y : ℤ) : Dart.behindRight ⟨x, y, Dir.S⟩ = (x - 1, y) := rfl



end SteinhausWalk

end RHTower

/-!
## The walk: region lemmas, step invariants, termination, shores, exits

`Good` darts (free on the left, marked on the right) are closed under `succ` except at frame
exits; `pred` inverts `succ` on `Good` darts; the walk from the pinned start dart (wedged between
the free corner `(-1,-1)` and the marked bottom sentinel `(0,-1)`) cannot repeat and must exit;
along the way the marked right shore stays king-connected to the bottom sentinel and the free left
shore stays rook-connected to the left sentinel; the exit hands one of the shores its opposite
sentinel, and the interior of that sentinel-to-sentinel chain is the crossing of the original
board.
-/

namespace RHTower

namespace SteinhausWalk

open Relation

section Walk

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- King adjacency on the padded integer board. -/
def kingAdjZ (a b : ℤ × ℤ) : Prop :=
  a ≠ b ∧ a.1 ≤ b.1 + 1 ∧ b.1 ≤ a.1 + 1 ∧ a.2 ≤ b.2 + 1 ∧ b.2 ≤ a.2 + 1

/-- Rook adjacency on the padded integer board. -/
def rookAdjZ (a b : ℤ × ℤ) : Prop :=
  (a.1 = b.1 ∧ (a.2 = b.2 + 1 ∨ b.2 = a.2 + 1)) ∨
    (a.2 = b.2 ∧ (a.1 = b.1 + 1 ∨ b.1 = a.1 + 1))

/-- A king step between marked cells of the padded board. -/
def augKingStep (a b : ℤ × ℤ) : Prop :=
  kingAdjZ a b ∧ clr Mk a = Color.marked ∧ clr Mk b = Color.marked

/-- A rook step between free cells of the padded board. -/
def augRookStep (a b : ℤ × ℤ) : Prop :=
  rookAdjZ a b ∧ clr Mk a = Color.free ∧ clr Mk b = Color.free

/-- A free cell is a left sentinel, a right sentinel, or an interior cell with the original
marking false. -/
theorem free_cases {c : ℤ × ℤ} (h : clr Mk c = Color.free) :
    (c.1 = -1 ∧ -1 ≤ c.2 ∧ c.2 ≤ (n : ℤ)) ∨ (c.1 = (m : ℤ) + 1 ∧ 0 ≤ c.2 ∧ c.2 ≤ (n : ℤ)) ∨
      ((0 ≤ c.1 ∧ c.1 ≤ (m : ℤ)) ∧ (0 ≤ c.2 ∧ c.2 ≤ (n : ℤ))) := by
  simp only [clr] at h
  split_ifs at h with a1 a2 a3 a4 a5 a6
  · exact Or.inl ⟨a1.1, a1.2.1, a1.2.2⟩
  · exact Or.inr (Or.inl ⟨a2.1, a2.2.1, a2.2.2⟩)
  · exact Or.inr (Or.inr a5)

/-- A marked cell is a bottom sentinel, a top sentinel, or an interior cell with the original
marking true. -/
theorem marked_cases {c : ℤ × ℤ} (h : clr Mk c = Color.marked) :
    ((0 ≤ c.1 ∧ c.1 ≤ (m : ℤ)) ∧ c.2 = -1) ∨ ((0 ≤ c.1 ∧ c.1 ≤ (m : ℤ)) ∧ c.2 = (n : ℤ) + 1) ∨
      ((0 ≤ c.1 ∧ c.1 ≤ (m : ℤ)) ∧ (0 ≤ c.2 ∧ c.2 ≤ (n : ℤ))) := by
  simp only [clr] at h
  split_ifs at h with a1 a2 a3 a4 a5 a6
  · exact Or.inl a3
  · exact Or.inr (Or.inl a4)
  · exact Or.inr (Or.inr a5)

/-- The interior reading of a marked interior cell. -/
theorem marked_interior {c : ℤ × ℤ} (h : clr Mk c = Color.marked)
    (hi : 0 ≤ c.1) (hi' : c.1 ≤ (m : ℤ)) (hj : 0 ≤ c.2) (hj' : c.2 ≤ (n : ℤ)) :
    Mk (⟨c.1.toNat, by omega⟩, ⟨c.2.toNat, by omega⟩) := by
  simp only [clr] at h
  split_ifs at h with a1 a2 a3 a4 a5 a6
  · exact absurd a3.2 (by omega)
  · exact absurd a4.2 (by omega)
  · exact a6

/-- The interior reading of a free interior cell. -/
theorem free_interior {c : ℤ × ℤ} (h : clr Mk c = Color.free)
    (hi : 0 ≤ c.1) (hi' : c.1 ≤ (m : ℤ)) (hj' : c.2 ≤ (n : ℤ)) :
    ¬ Mk (⟨c.1.toNat, by omega⟩, ⟨c.2.toNat, by omega⟩) := by
  simp only [clr] at h
  split_ifs at h with a1 a2 a3 a4 a5 a6
  · exact absurd a1.1 (by omega)
  · exact absurd a2.1 (by omega)
  · exact a6

/-- The bottom sentinel row is marked. -/
theorem clr_bottom {c : ℤ × ℤ} (hi : 0 ≤ c.1) (hi' : c.1 ≤ (m : ℤ)) (hj : c.2 = -1) :
    clr Mk c = Color.marked := by
  simp only [clr]
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | rfl | (exfalso; omega)

/-- The top sentinel row is marked. -/
theorem clr_top {c : ℤ × ℤ} (hi : 0 ≤ c.1) (hi' : c.1 ≤ (m : ℤ)) (hj : c.2 = (n : ℤ) + 1) :
    clr Mk c = Color.marked := by
  simp only [clr]
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | rfl | (exfalso; omega)

/-- The left sentinel column is free. -/
theorem clr_left {c : ℤ × ℤ} (hi : c.1 = -1) (hj : -1 ≤ c.2) (hj' : c.2 ≤ (n : ℤ)) :
    clr Mk c = Color.free := by
  simp only [clr]
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | rfl | (exfalso; omega)

/-- The right sentinel column is free. -/
theorem clr_right {c : ℤ × ℤ} (hi : c.1 = (m : ℤ) + 1) (hj : 0 ≤ c.2) (hj' : c.2 ≤ (n : ℤ)) :
    clr Mk c = Color.free := by
  simp only [clr]
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | rfl | (exfalso; omega)

/-- Cells outside the padded bounding box are neutral (not marked). -/
theorem not_marked_outside {c : ℤ × ℤ}
    (h : c.1 < -1 ∨ (m : ℤ) + 1 < c.1 ∨ c.2 < -1 ∨ (n : ℤ) + 1 < c.2) :
    clr Mk c ≠ Color.marked := by
  intro hm
  rcases marked_cases Mk hm with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega

/-- Cells outside the padded bounding box are neutral (not free). -/
theorem not_free_outside {c : ℤ × ℤ}
    (h : c.1 < -1 ∨ (m : ℤ) + 1 < c.1 ∨ c.2 < -1 ∨ (n : ℤ) + 1 < c.2) :
    clr Mk c ≠ Color.free := by
  intro hm
  rcases free_cases Mk hm with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega

end Walk

end SteinhausWalk

end RHTower

namespace RHTower

namespace SteinhausWalk

open Relation

section Steps

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- Within the padded bounding box, every cell except the three neutral corners is coloured. -/
theorem clr_ne_neutral {c : ℤ × ℤ}
    (h1 : -1 ≤ c.1) (h2 : c.1 ≤ (m : ℤ) + 1) (h3 : -1 ≤ c.2) (h4 : c.2 ≤ (n : ℤ) + 1)
    (hc1 : ¬(c.1 = (m : ℤ) + 1 ∧ c.2 = -1)) (hc2 : ¬(c.1 = (m : ℤ) + 1 ∧ c.2 = (n : ℤ) + 1))
    (hc3 : ¬(c.1 = -1 ∧ c.2 = (n : ℤ) + 1)) :
    clr Mk c ≠ Color.neutral := by
  simp only [clr]
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | (simp; done) | (exfalso; omega)

/-- A cell that is not marked, within the box and off the neutral corners, is free. -/
theorem free_of_not_marked {c : ℤ × ℤ} (hm : clr Mk c ≠ Color.marked)
    (h1 : -1 ≤ c.1) (h2 : c.1 ≤ (m : ℤ) + 1) (h3 : -1 ≤ c.2) (h4 : c.2 ≤ (n : ℤ) + 1)
    (hc1 : ¬(c.1 = (m : ℤ) + 1 ∧ c.2 = -1)) (hc2 : ¬(c.1 = (m : ℤ) + 1 ∧ c.2 = (n : ℤ) + 1))
    (hc3 : ¬(c.1 = -1 ∧ c.2 = (n : ℤ) + 1)) :
    clr Mk c = Color.free := by
  have hn := clr_ne_neutral Mk h1 h2 h3 h4 hc1 hc2 hc3
  cases h : clr Mk c
  · exact absurd h hm
  · rfl
  · exact absurd h hn

/-- **Successor specification.**  The three branches of the walk rule, with the cells of the
successor dart identified among the cells of the current dart. -/
theorem succ_spec (t : Dart) :
    (clr Mk t.aheadLeft = Color.marked ∧
      (succ Mk t).leftCell = t.leftCell ∧ (succ Mk t).rightCell = t.aheadLeft) ∨
    (clr Mk t.aheadLeft ≠ Color.marked ∧ clr Mk t.aheadRight = Color.marked ∧
      (succ Mk t).leftCell = t.aheadLeft ∧ (succ Mk t).rightCell = t.aheadRight) ∨
    (clr Mk t.aheadLeft ≠ Color.marked ∧ clr Mk t.aheadRight ≠ Color.marked ∧
      (succ Mk t).leftCell = t.aheadRight ∧ (succ Mk t).rightCell = t.rightCell) := by
  obtain ⟨x, y, d⟩ := t
  by_cases h1 : clr Mk (Dart.aheadLeft ⟨x, y, d⟩) = Color.marked
  · refine Or.inl ⟨h1, ?_, ?_⟩ <;>
    · unfold succ
      rw [if_pos h1]
      cases d <;>
        simp [Dart.leftCell, Dart.rightCell, Dart.aheadLeft, Dir.vec, Dir.ccw,
          Prod.mk.injEq] <;> omega
  · by_cases h2 : clr Mk (Dart.aheadRight ⟨x, y, d⟩) = Color.marked
    · refine Or.inr (Or.inl ⟨h1, h2, ?_, ?_⟩) <;>
      · unfold succ
        rw [if_neg h1, if_pos h2]
        cases d <;>
          simp [Dart.leftCell, Dart.rightCell, Dart.aheadLeft, Dart.aheadRight, Dir.vec,
            Prod.mk.injEq] <;> omega
    · refine Or.inr (Or.inr ⟨h1, h2, ?_, ?_⟩) <;>
      · unfold succ
        rw [if_neg h1, if_neg h2]
        cases d <;>
          simp [Dart.leftCell, Dart.rightCell, Dart.aheadRight, Dir.vec, Dir.cw,
            Prod.mk.injEq] <;> omega

/-- **Predecessor inversion.**  On a `Good` dart the walk is injective: `pred` undoes `succ`. -/
theorem pred_succ (t : Dart) (hG : Good Mk t) : pred Mk (succ Mk t) = t := by
  obtain ⟨hL, hR⟩ := hG
  obtain ⟨x, y, d⟩ := t
  by_cases h1 : clr Mk (Dart.aheadLeft ⟨x, y, d⟩) = Color.marked
  · unfold succ
    rw [if_pos h1]
    unfold pred
    cases d <;>
      · simp only [Dart.leftCell, Dart.rightCell, Dart.aheadLeft,
          Dart.behindLeft, Dart.behindRight, Dir.vec, Dir.ccw, Dir.cw] at *
        try simp at *
        try ring_nf at *
        try simp [hR]
        try omega
  · by_cases h2 : clr Mk (Dart.aheadRight ⟨x, y, d⟩) = Color.marked
    · unfold succ
      rw [if_neg h1, if_pos h2]
      unfold pred
      cases d <;>
        · simp only [Dart.leftCell, Dart.rightCell, Dart.aheadLeft, Dart.aheadRight,
            Dart.behindLeft, Dart.behindRight, Dir.vec, Dir.ccw, Dir.cw] at *
          try simp at *
          try ring_nf at *
          try simp [hL, hR]
          try omega
    · unfold succ
      rw [if_neg h1, if_neg h2]
      unfold pred
      cases d <;>
        · simp only [Dart.leftCell, Dart.rightCell, Dart.aheadLeft, Dart.aheadRight,
            Dart.behindLeft, Dart.behindRight, Dir.vec, Dir.ccw, Dir.cw] at *
          try simp at *
          try ring_nf at *
          try simp [hL, h1]
          try omega

end Steps

end SteinhausWalk

end RHTower

namespace RHTower

namespace SteinhausWalk

open Relation

section Shores

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

instance (t : Dart) : Decidable (Good Mk t) := by unfold Good; infer_instance

/-- The first walk branch always preserves the invariant. -/
theorem good_succ_case1 {t : Dart} (hG : Good Mk t)
    (h1 : clr Mk t.aheadLeft = Color.marked) : Good Mk (succ Mk t) := by
  rcases succ_spec Mk t with ⟨_, hl, hr⟩ | ⟨hno, _, _, _⟩ | ⟨hno, _, _, _⟩
  · exact ⟨hl ▸ hG.1, hr ▸ h1⟩
  · exact absurd h1 hno
  · exact absurd h1 hno

/-- **Marked-shore step.**  Along a `Good`-to-`Good` walk step the marked right cell stays put or
makes one king step. -/
theorem shore_marked_step {t : Dart} (hG : Good Mk t) (hG' : Good Mk (succ Mk t)) :
    Relation.ReflTransGen (augKingStep Mk) t.rightCell (succ Mk t).rightCell := by
  rcases succ_spec Mk t with ⟨h1, hl, hr⟩ | ⟨h1, h2, hl, hr⟩ | ⟨h1, h2, hl, hr⟩
  · -- turn left: right cell moves to the diagonal ahead-left cell.
    refine Relation.ReflTransGen.single ⟨?_, hG.2, hr ▸ hG'.2⟩
    rw [hr]
    obtain ⟨x, y, d⟩ := t
    cases d <;>
      · simp [kingAdjZ, Dart.rightCell, Dart.aheadLeft, ne_eq, Prod.mk.injEq]
        try omega
  · -- straight: right cell advances one rook (hence king) step.
    refine Relation.ReflTransGen.single ⟨?_, hG.2, hr ▸ hG'.2⟩
    rw [hr]
    obtain ⟨x, y, d⟩ := t
    cases d <;>
      · simp [kingAdjZ, Dart.rightCell, Dart.aheadRight, ne_eq, Prod.mk.injEq]
        try omega
  · rw [hr]

/-- In the third walk branch of a `Good`-to-`Good` step, the diagonal ahead-left cell is free (it
cannot be neutral: the surrounding coloured cells pin it inside the box, off the neutral corners).
-/
theorem case3_aheadLeft_free {t : Dart} (hG : Good Mk t)
    (h1 : clr Mk t.aheadLeft ≠ Color.marked) (h2 : clr Mk t.aheadRight ≠ Color.marked)
    (haR : clr Mk t.aheadRight = Color.free) :
    clr Mk t.aheadLeft = Color.free := by
  obtain ⟨hL, hR⟩ := hG
  have hLb := free_cases Mk hL
  have hRb := marked_cases Mk hR
  have haRb := free_cases Mk haR
  obtain ⟨x, y, d⟩ := t
  refine free_of_not_marked Mk h1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    cases d <;>
      · (try simp at hLb hRb haRb ⊢); omega

/-- **Free-shore step.**  Along a `Good`-to-`Good` walk step the free left cell stays put or makes
one or two rook steps (the two-step case passes through the free diagonal cell of the right turn).
-/
theorem shore_free_step {t : Dart} (hG : Good Mk t) (hG' : Good Mk (succ Mk t)) :
    Relation.ReflTransGen (augRookStep Mk) t.leftCell (succ Mk t).leftCell := by
  rcases succ_spec Mk t with ⟨h1, hl, hr⟩ | ⟨h1, h2, hl, hr⟩ | ⟨h1, h2, hl, hr⟩
  · rw [hl]
  · -- straight: left cell advances one rook step.
    refine Relation.ReflTransGen.single ⟨?_, hG.1, hl ▸ hG'.1⟩
    rw [hl]
    obtain ⟨x, y, d⟩ := t
    cases d <;>
      · simp [rookAdjZ, Dart.leftCell, Dart.aheadLeft]
        try omega
  · -- turn right: left → aheadLeft → aheadRight, both rook steps through free cells.
    have haR : clr Mk t.aheadRight = Color.free := hl ▸ hG'.1
    have haL : clr Mk t.aheadLeft = Color.free := case3_aheadLeft_free Mk hG h1 h2 haR
    refine Relation.ReflTransGen.head ⟨?_, hG.1, haL⟩ (Relation.ReflTransGen.single ⟨?_, haL, hl ▸ haR⟩)
    · obtain ⟨x, y, d⟩ := t
      cases d <;>
        · simp [rookAdjZ]
          try omega
    · rw [hl]
      obtain ⟨x, y, d⟩ := t
      cases d <;>
        · simp [rookAdjZ]
          try omega

end Shores

end SteinhausWalk

end RHTower

namespace RHTower

namespace SteinhausWalk

open Relation

section TheWalk

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- The pinned start dart: heading north along the crack between the free corner `(-1,-1)` and the
marked bottom-sentinel cell `(0,-1)`. -/
def startDart : Dart := ⟨0, -1, Dir.N⟩

theorem good_startDart : Good Mk startDart := by
  constructor
  · show clr Mk (-1, -1) = Color.free
    exact clr_left Mk (by norm_num) (by norm_num) (by norm_num)
  · show clr Mk (0, -1) = Color.marked
    exact clr_bottom Mk (by norm_num) (by norm_num) (by norm_num)

/-- The start dart has no `Good` predecessor: the backward walk formula lands on a dart whose left
cell lies outside the padded box. -/
theorem no_pred_startDart (u : Dart) (hu : Good Mk u) : succ Mk u ≠ startDart := by
  intro hcon
  have hb1 : ¬ clr Mk (Dart.behindLeft (⟨0, -1, Dir.N⟩ : Dart)) = Color.marked :=
    not_marked_outside Mk (by norm_num [Dart.behindLeft])
  have hb2 : ¬ clr Mk (Dart.behindRight (⟨0, -1, Dir.N⟩ : Dart)) = Color.marked :=
    not_marked_outside Mk (by norm_num [Dart.behindRight])
  have hpredval : pred Mk startDart = ⟨1, -1, Dir.W⟩ := by
    unfold pred startDart
    rw [if_neg hb1, if_neg hb2]
    norm_num [Dir.ccw, Dir.vec]
  have hpred : u = pred Mk startDart := by
    rw [← hcon, pred_succ Mk u hu]
  rw [hpredval] at hpred
  subst hpred
  have hfree : clr Mk ((0 : ℤ), (-2 : ℤ)) = Color.free := by
    have h0 := hu.1
    simp only [Dart.leftCell] at h0
    norm_num at h0
    exact h0
  exact not_free_outside Mk (by omega) hfree

/-- The finite box containing every `Good` dart's data. -/
noncomputable def dartBox : Finset ((ℤ × ℤ) × Dir) :=
  ((Finset.Icc (-2 : ℤ) ((m : ℤ) + 2)) ×ˢ (Finset.Icc (-2 : ℤ) ((n : ℤ) + 2))) ×ˢ
    ({Dir.E, Dir.N, Dir.W, Dir.S} : Finset Dir)

theorem good_mem_dartBox {t : Dart} (h : Good Mk t) :
    ((t.x, t.y), t.d) ∈ dartBox (m := m) (n := n) := by
  have hb := free_cases Mk h.1
  obtain ⟨x, y, d⟩ := t
  unfold dartBox
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · cases d <;> ((try simp at hb ⊢); omega)
  · cases d <;> ((try simp at hb ⊢); omega)
  · cases d <;> simp

/-- The walk: iterate the successor from the start dart. -/
def walk (k : ℕ) : Dart := (succ Mk)^[k] startDart

/-- If every prefix of the walk is `Good`, two iterates collide and the collision backs up to a
`Good` predecessor of the start dart — impossible.  So some iterate fails `Good`. -/
theorem exists_bad : ∃ k, ¬ Good Mk (walk Mk k) := by
  by_contra hcon
  push Not at hcon
  -- backstepping along all-Good iterates
  have hback : ∀ i k, walk Mk (i + k) = walk Mk i → walk Mk k = walk Mk 0 := by
    intro i
    induction i with
    | zero => intro k h; simpa using h
    | succ i ih =>
      intro k h
      have h1 : walk Mk (i + k + 1) = walk Mk (i + 1) := by
        rw [show i + 1 + k = i + k + 1 from by omega] at h
        exact h
      have h2 : walk Mk (i + k) = walk Mk i := by
        have e1 : walk Mk (i + k + 1) = succ Mk (walk Mk (i + k)) :=
          Function.iterate_succ_apply' _ _ _
        have e2 : walk Mk (i + 1) = succ Mk (walk Mk i) :=
          Function.iterate_succ_apply' _ _ _
        have := h1
        rw [e1, e2] at this
        have p1 := pred_succ Mk (walk Mk (i + k)) (hcon _)
        have p2 := pred_succ Mk (walk Mk i) (hcon _)
        rw [← p1, ← p2, this]
      exact ih k h2
  -- pigeonhole on the finite dart box
  have hmap : ∀ k ∈ Finset.range ((dartBox (m := m) (n := n)).card + 1),
      (((walk Mk k).x, (walk Mk k).y), (walk Mk k).d) ∈ dartBox (m := m) (n := n) := by
    intro k _
    exact good_mem_dartBox Mk (hcon k)
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by rw [Finset.card_range]; omega) hmap
  -- recover dart equality from data equality
  have hdart : walk Mk i = walk Mk j := by
    have h1 : (walk Mk i).x = (walk Mk j).x := by
      have := congrArg (fun p => p.1.1) heq; simpa using this
    have h2 : (walk Mk i).y = (walk Mk j).y := by
      have := congrArg (fun p => p.1.2) heq; simpa using this
    have h3 : (walk Mk i).d = (walk Mk j).d := by
      have := congrArg (fun p => p.2) heq; simpa using this
    cases hw : walk Mk i
    cases hw' : walk Mk j
    rw [hw, hw'] at h1 h2 h3
    simp_all
  -- order the collision and derive the impossible predecessor
  rcases Nat.lt_or_ge i j with hlt | hge
  · have h0 : walk Mk (j - i) = walk Mk 0 := by
      have := hback i (j - i) (by rw [show i + (j - i) = j from by omega]; exact hdart.symm)
      exact this
    have hpos : 1 ≤ j - i := by omega
    have hstep : walk Mk (j - i) = succ Mk (walk Mk (j - i - 1)) := by
      rw [show j - i = (j - i - 1) + 1 from by omega]
      exact Function.iterate_succ_apply' _ _ _
    exact no_pred_startDart Mk _ (hcon _) (by rw [← hstep, h0]; rfl)
  · have hlt' : j < i := by omega
    have h0 : walk Mk (i - j) = walk Mk 0 := by
      have := hback j (i - j) (by rw [show j + (i - j) = i from by omega]; exact hdart)
      exact this
    have hpos : 1 ≤ i - j := by omega
    have hstep : walk Mk (i - j) = succ Mk (walk Mk (i - j - 1)) := by
      rw [show i - j = (i - j - 1) + 1 from by omega]
      exact Function.iterate_succ_apply' _ _ _
    exact no_pred_startDart Mk _ (hcon _) (by rw [← hstep, h0]; rfl)

/-- The exit index: the first walk position whose successor state fails the invariant. -/
noncomputable def exitIndex : ℕ := Nat.find (exists_bad Mk)

theorem exit_pos : 1 ≤ exitIndex Mk := by
  rcases Nat.eq_zero_or_pos (exitIndex Mk) with h | h
  · exfalso
    have := Nat.find_spec (exists_bad Mk)
    rw [show Nat.find (exists_bad Mk) = exitIndex Mk from rfl, h] at this
    exact this (good_startDart Mk)
  · exact h

theorem good_before_exit {k : ℕ} (h : k < exitIndex Mk) : Good Mk (walk Mk k) := by
  by_contra hcon
  have hle : exitIndex Mk ≤ k := Nat.find_le hcon
  omega

theorem bad_at_exit : ¬ Good Mk (walk Mk (exitIndex Mk)) := Nat.find_spec (exists_bad Mk)

/-- The exit dart: the last `Good` state of the walk. -/
noncomputable def exitDart : Dart := walk Mk (exitIndex Mk - 1)

theorem good_exitDart : Good Mk (exitDart Mk) :=
  good_before_exit Mk (by have := exit_pos Mk; omega)

theorem bad_succ_exitDart : ¬ Good Mk (succ Mk (exitDart Mk)) := by
  have hstep : walk Mk (exitIndex Mk) = succ Mk (exitDart Mk) := by
    unfold exitDart
    rw [show exitIndex Mk = (exitIndex Mk - 1) + 1 from by have := exit_pos Mk; omega]
    exact Function.iterate_succ_apply' _ _ _
  rw [← hstep]
  exact bad_at_exit Mk

/-- **Marked shore accumulation.**  The marked right cell of every walk state before the exit is
king-reachable from the bottom-sentinel start `(0,-1)`. -/
theorem shore_marked_reach : ∀ k, k < exitIndex Mk →
    Relation.ReflTransGen (augKingStep Mk) ((0 : ℤ), (-1 : ℤ)) (walk Mk k).rightCell := by
  intro k
  induction k with
  | zero =>
    intro _
    have : (walk Mk 0).rightCell = ((0 : ℤ), (-1 : ℤ)) := by
      show (startDart : Dart).rightCell = _
      norm_num [startDart, Dart.rightCell]
    rw [this]
  | succ k ih =>
    intro hk
    have hstep : walk Mk (k + 1) = succ Mk (walk Mk k) := Function.iterate_succ_apply' _ _ _
    rw [hstep]
    exact (ih (by omega)).trans
      (shore_marked_step Mk (good_before_exit Mk (by omega))
        (by rw [← hstep]; exact good_before_exit Mk hk))

/-- **Free shore accumulation.**  The free left cell of every walk state before the exit is
rook-reachable from the left-sentinel corner `(-1,-1)`. -/
theorem shore_free_reach : ∀ k, k < exitIndex Mk →
    Relation.ReflTransGen (augRookStep Mk) ((-1 : ℤ), (-1 : ℤ)) (walk Mk k).leftCell := by
  intro k
  induction k with
  | zero =>
    intro _
    have : (walk Mk 0).leftCell = ((-1 : ℤ), (-1 : ℤ)) := by
      show (startDart : Dart).leftCell = _
      norm_num [startDart, Dart.leftCell]
    rw [this]
  | succ k ih =>
    intro hk
    have hstep : walk Mk (k + 1) = succ Mk (walk Mk k) := Function.iterate_succ_apply' _ _ _
    rw [hstep]
    exact (ih (by omega)).trans
      (shore_free_step Mk (good_before_exit Mk (by omega))
        (by rw [← hstep]; exact good_before_exit Mk hk))

end TheWalk

end SteinhausWalk

end RHTower

namespace RHTower

namespace SteinhausWalk

open Relation

section Exit

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- **Exit classification.**  At the exit dart one of the shores meets its opposite sentinel:
either the marked shore extends to a top-sentinel cell, or the free shore extends to a
right-sentinel cell. -/
theorem exit_classification :
    (∃ c : ℤ × ℤ, Relation.ReflTransGen (augKingStep Mk) ((0 : ℤ), (-1 : ℤ)) c ∧
      c.2 = (n : ℤ) + 1) ∨
    (∃ c : ℤ × ℤ, Relation.ReflTransGen (augRookStep Mk) ((-1 : ℤ), (-1 : ℤ)) c ∧
      c.1 = (m : ℤ) + 1) := by
  set t := exitDart Mk with ht
  have hG : Good Mk t := good_exitDart Mk
  have hbad : ¬ Good Mk (succ Mk t) := bad_succ_exitDart Mk
  have hKidx : exitIndex Mk - 1 < exitIndex Mk := by have := exit_pos Mk; omega
  have hMreach := shore_marked_reach Mk (exitIndex Mk - 1) hKidx
  have hFreach := shore_free_reach Mk (exitIndex Mk - 1) hKidx
  rw [show walk Mk (exitIndex Mk - 1) = t from rfl] at hMreach hFreach
  have hLb := free_cases Mk hG.1
  have hRb := marked_cases Mk hG.2
  rcases succ_spec Mk t with ⟨h1, hl, hr⟩ | ⟨h1, h2, hl, hr⟩ | ⟨h1, h2, hl, hr⟩
  · exact absurd (good_succ_case1 Mk hG h1) hbad
  · -- straight branch exit: ahead-left is not free.
    have haL : clr Mk t.aheadLeft ≠ Color.free := by
      intro hfree
      exact hbad ⟨hl ▸ hfree, hr ▸ h2⟩
    have haRb := marked_cases Mk h2
    -- either the ahead-right marked cell is a top sentinel, or the left cell is a right sentinel
    have hkey : t.aheadRight.2 = (n : ℤ) + 1 ∨ t.leftCell.1 = (m : ℤ) + 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      apply haL
      refine free_of_not_marked Mk h1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        · obtain ⟨x, y, d⟩ := t
          cases d <;>
            · (try simp at hLb hRb haRb hc1 hc2 ⊢); omega
    rcases hkey with htop | hright
    · -- marked crossing: append the king step to the ahead-right top cell.
      refine Or.inl ⟨t.aheadRight, hMreach.tail ⟨?_, hG.2, h2⟩, htop⟩
      obtain ⟨x, y, d⟩ := t
      cases d <;>
        · simp only [Dart.rightCell, Dart.aheadRight, kingAdjZ, ne_eq, Prod.ext_iff]
          refine ⟨by intro hcon; omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨t.leftCell, hFreach, hright⟩
  · -- right-turn branch exit: ahead-right is not free.
    have haR : clr Mk t.aheadRight ≠ Color.free := by
      intro hfree
      exact hbad ⟨hl ▸ hfree, hr ▸ hG.2⟩
    have hkey : t.rightCell.2 = (n : ℤ) + 1 ∨
        (t.aheadLeft.1 = (m : ℤ) + 1 ∧ 0 ≤ t.aheadLeft.2 ∧ t.aheadLeft.2 ≤ (n : ℤ)) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      apply haR
      refine free_of_not_marked Mk h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        · obtain ⟨x, y, d⟩ := t
          cases d <;>
            · (try simp at hLb hRb hc1 hc2 ⊢); omega
    rcases hkey with htop | ⟨hright, hj0, hj1⟩
    · exact Or.inl ⟨t.rightCell, hMreach, htop⟩
    · -- free crossing: append the rook step to the ahead-left right-sentinel cell.
      have haLfree : clr Mk t.aheadLeft = Color.free :=
        clr_right Mk hright hj0 hj1
      refine Or.inr ⟨t.aheadLeft, hFreach.tail ⟨?_, hG.1, haLfree⟩, hright⟩
      obtain ⟨x, y, d⟩ := t
      cases d <;>
        · simp [rookAdjZ]
          try omega

end Exit

section Extract

/-- Last visit to `S`: any reachability from an `S`-point refines to reachability from a possibly
later `S`-point through steps that never re-enter `S`. -/
theorem reach_extract_last {α : Type*} {r : α → α → Prop} {S : α → Prop} :
    ∀ {a b : α}, Relation.ReflTransGen r a b → S a →
      ∃ u, S u ∧ Relation.ReflTransGen (fun p q => r p q ∧ ¬ S q) u b := by
  intro a b h
  induction h with
  | refl => intro ha; exact ⟨a, ha, Relation.ReflTransGen.refl⟩
  | @tail c b h' step ih =>
    intro ha
    by_cases hSb : S b
    · exact ⟨b, hSb, Relation.ReflTransGen.refl⟩
    · obtain ⟨u, hu, hchain⟩ := ih ha
      exact ⟨u, hu, hchain.tail ⟨step, hSb⟩⟩

/-- First visit to `T`: any reachability into a `T`-point refines to reachability into a possibly
earlier `T`-point through steps that never start in `T`. -/
theorem reach_extract_first {α : Type*} {r : α → α → Prop} {T : α → Prop} :
    ∀ {a b : α}, Relation.ReflTransGen r a b → T b →
      ∃ v, T v ∧ Relation.ReflTransGen (fun p q => r p q ∧ ¬ T p) a v := by
  intro a b h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro hb; exact ⟨b, hb, Relation.ReflTransGen.refl⟩
  | @head x y step h' ih =>
    intro hb
    by_cases hTx : T x
    · exact ⟨x, hTx, Relation.ReflTransGen.refl⟩
    · obtain ⟨v, hv, hchain⟩ := ih hb
      exact ⟨v, hv, hchain.head ⟨step, hTx⟩⟩

end Extract

end SteinhausWalk

end RHTower

namespace RHTower

namespace SteinhausWalk

open Relation

section Pipelines

variable {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) [DecidablePred Mk]

/-- Along a chain whose steps never re-enter `S`, the endpoint stays out of `S` unless the chain is
trivial. -/
theorem rtg_target_prop {α : Type*} {r : α → α → Prop} {P : α → Prop}
    (hP : ∀ p q, r p q → P q) : ∀ {a b : α}, Relation.ReflTransGen r a b → a = b ∨ P b := by
  intro a b h
  induction h with
  | refl => exact Or.inl rfl
  | @tail c b h' step _ => exact Or.inr (hP _ _ step)

/-- Interior conversion, marked side: a sentinel-free king chain between interior cells descends to
the board. -/
theorem king_chain_toFin :
    ∀ {a b : ℤ × ℤ},
      Relation.ReflTransGen
        (fun p q => (augKingStep Mk p q ∧ q.2 ≠ -1) ∧ p.2 ≠ (n : ℤ) + 1) a b →
      ∀ (ha : 0 ≤ a.1 ∧ a.1 ≤ (m : ℤ) ∧ 0 ≤ a.2 ∧ a.2 ≤ (n : ℤ))
        (hb : 0 ≤ b.1 ∧ b.1 ≤ (m : ℤ) ∧ 0 ≤ b.2 ∧ b.2 ≤ (n : ℤ)),
      markReach Mk (⟨a.1.toNat, by omega⟩, ⟨a.2.toNat, by omega⟩)
        (⟨b.1.toNat, by omega⟩, ⟨b.2.toNat, by omega⟩) := by
  intro a b h
  induction h with
  | refl => intro _ _; exact Relation.ReflTransGen.refl
  | @tail q b h' step ih =>
    intro ha hb
    obtain ⟨⟨hks, hq2⟩, hqtop⟩ := step
    -- the intermediate source cell is interior
    have hqmk : clr Mk q = Color.marked := hks.2.1
    have hq_ne : q.2 ≠ -1 := by
      rcases rtg_target_prop (fun p q hpq => hpq.1.2) h' with heq | hne
      · rw [← heq]; omega
      · exact hne
    have hqint : 0 ≤ q.1 ∧ q.1 ≤ (m : ℤ) ∧ 0 ≤ q.2 ∧ q.2 ≤ (n : ℤ) := by
      rcases marked_cases Mk hqmk with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
    refine (ih ha hqint).tail ⟨?_, ?_, ?_⟩
    · -- king adjacency descends
      obtain ⟨hne, k1, k2, k3, k4⟩ := hks.1
      refine ⟨⟨by simp; omega, by simp; omega⟩, ⟨by simp; omega, by simp; omega⟩, ?_⟩
      intro hcon
      apply hne
      rw [Prod.mk.injEq] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have e1 : q.1.toNat = b.1.toNat := congrArg Fin.val hc1
      have e2 : q.2.toNat = b.2.toNat := congrArg Fin.val hc2
      have : q.1 = b.1 := by omega
      have : q.2 = b.2 := by omega
      exact Prod.ext (by omega) (by omega)
    · exact marked_interior Mk hqmk hqint.1 hqint.2.1 hqint.2.2.1 hqint.2.2.2
    · exact marked_interior Mk hks.2.2 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

/-- Interior conversion, free side: a sentinel-free rook chain between interior cells descends to
the board. -/
theorem rook_chain_toFin :
    ∀ {a b : ℤ × ℤ},
      Relation.ReflTransGen
        (fun p q => (augRookStep Mk p q ∧ q.1 ≠ -1) ∧ p.1 ≠ (m : ℤ) + 1) a b →
      ∀ (ha : 0 ≤ a.1 ∧ a.1 ≤ (m : ℤ) ∧ 0 ≤ a.2 ∧ a.2 ≤ (n : ℤ))
        (hb : 0 ≤ b.1 ∧ b.1 ≤ (m : ℤ) ∧ 0 ≤ b.2 ∧ b.2 ≤ (n : ℤ)),
      freeReach Mk (⟨a.1.toNat, by omega⟩, ⟨a.2.toNat, by omega⟩)
        (⟨b.1.toNat, by omega⟩, ⟨b.2.toNat, by omega⟩) := by
  intro a b h
  induction h with
  | refl => intro _ _; exact Relation.ReflTransGen.refl
  | @tail q b h' step ih =>
    intro ha hb
    obtain ⟨⟨hrs, hq1⟩, hqright⟩ := step
    have hqfr : clr Mk q = Color.free := hrs.2.1
    have hq_ne : q.1 ≠ -1 := by
      rcases rtg_target_prop (fun p q hpq => hpq.1.2) h' with heq | hne
      · rw [← heq]; omega
      · exact hne
    have hqint : 0 ≤ q.1 ∧ q.1 ≤ (m : ℤ) ∧ 0 ≤ q.2 ∧ q.2 ≤ (n : ℤ) := by
      rcases free_cases Mk hqfr with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
    refine (ih ha hqint).tail ⟨?_, ?_, ?_⟩
    · -- rook adjacency descends
      rcases hrs.1 with ⟨hcol, hstep⟩ | ⟨hrow, hstep⟩
      · refine Or.inl ⟨?_, ?_⟩
        · exact Fin.ext (by simp; omega)
        · rcases hstep with h | h
          · exact Or.inr (by simp; omega)
          · exact Or.inl (by simp; omega)
      · refine Or.inr ⟨?_, ?_⟩
        · exact Fin.ext (by simp; omega)
        · rcases hstep with h | h
          · exact Or.inr (by simp; omega)
          · exact Or.inl (by simp; omega)
    · exact free_interior Mk hqfr hqint.1 hqint.2.1 hqint.2.2.2
    · exact free_interior Mk hrs.2.2 hb.1 hb.2.1 hb.2.2.2

/-- **Marked pipeline.**  An augmented king chain from the bottom-sentinel start to a top-sentinel
cell yields an interior marked king crossing of the original board. -/
theorem marked_pipeline
    (h : ∃ c : ℤ × ℤ, Relation.ReflTransGen (augKingStep Mk) ((0 : ℤ), (-1 : ℤ)) c ∧
      c.2 = (n : ℤ) + 1) :
    ∃ a b : Fin (m + 1) × Fin (n + 1),
      Mk a ∧ Mk b ∧ a.2 = 0 ∧ b.2 = Fin.last n ∧ markReach Mk a b := by
  obtain ⟨c, hchain, hc⟩ := h
  obtain ⟨u, hu, ch1⟩ := reach_extract_last (S := fun p : ℤ × ℤ => p.2 = -1) hchain rfl
  obtain ⟨v, hv, ch2⟩ := reach_extract_first (T := fun p : ℤ × ℤ => p.2 = (n : ℤ) + 1) ch1 hc
  -- peel the first step: lands on the bottom interior row
  rcases ch2.cases_head with heq | ⟨w, stw, ch3⟩
  · exfalso; rw [heq] at hu; omega
  · obtain ⟨⟨hkw, hw2⟩, _⟩ := stw
    have hwmk : clr Mk w = Color.marked := hkw.2.2
    have hw0 : w.2 = 0 := by
      obtain ⟨_, _, _, k3, k4⟩ := hkw.1
      have hb := marked_cases Mk hwmk
      omega
    have hwint : 0 ≤ w.1 ∧ w.1 ≤ (m : ℤ) ∧ 0 ≤ w.2 ∧ w.2 ≤ (n : ℤ) := by
      rcases marked_cases Mk hwmk with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
    -- peel the last step: departs from the top interior row
    rcases ch3.cases_tail with heq | ⟨p, ch4, stp⟩
    · exfalso; rw [heq] at hv; omega
    · obtain ⟨⟨hkp, _⟩, hptop⟩ := stp
      have hpmk : clr Mk p = Color.marked := hkp.2.1
      have hpn : p.2 = (n : ℤ) := by
        obtain ⟨_, _, _, k3, k4⟩ := hkp.1
        have hb := marked_cases Mk hpmk
        omega
      have hpint : 0 ≤ p.1 ∧ p.1 ≤ (m : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (n : ℤ) := by
        rcases marked_cases Mk hpmk with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
      refine ⟨(⟨w.1.toNat, by omega⟩, ⟨w.2.toNat, by omega⟩),
        (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩),
        marked_interior Mk hwmk hwint.1 hwint.2.1 hwint.2.2.1 hwint.2.2.2,
        marked_interior Mk hpmk hpint.1 hpint.2.1 hpint.2.2.1 hpint.2.2.2,
        ?_, ?_, king_chain_toFin Mk ch4 hwint hpint⟩
      · exact Fin.ext (by simp; omega)
      · exact Fin.ext (by simp [Fin.last]; omega)

/-- **Free pipeline.**  An augmented rook chain from the left-sentinel corner to a right-sentinel
cell yields an interior free rook crossing of the original board. -/
theorem free_pipeline
    (h : ∃ c : ℤ × ℤ, Relation.ReflTransGen (augRookStep Mk) ((-1 : ℤ), (-1 : ℤ)) c ∧
      c.1 = (m : ℤ) + 1) :
    ∃ a b : Fin (m + 1) × Fin (n + 1),
      ¬ Mk a ∧ ¬ Mk b ∧ a.1 = 0 ∧ b.1 = Fin.last m ∧ freeReach Mk a b := by
  obtain ⟨c, hchain, hc⟩ := h
  obtain ⟨u, hu, ch1⟩ := reach_extract_last (S := fun p : ℤ × ℤ => p.1 = -1) hchain rfl
  obtain ⟨v, hv, ch2⟩ := reach_extract_first (T := fun p : ℤ × ℤ => p.1 = (m : ℤ) + 1) ch1 hc
  rcases ch2.cases_head with heq | ⟨w, stw, ch3⟩
  · exfalso; rw [heq] at hu; omega
  · obtain ⟨⟨hrw, hw1⟩, _⟩ := stw
    have hwfr : clr Mk w = Color.free := hrw.2.2
    have hw0 : w.1 = 0 := by
      have hb := free_cases Mk hwfr
      rcases hrw.1 with ⟨hcol, hstep⟩ | ⟨hrow, hstep⟩ <;> omega
    have hwint : 0 ≤ w.1 ∧ w.1 ≤ (m : ℤ) ∧ 0 ≤ w.2 ∧ w.2 ≤ (n : ℤ) := by
      rcases free_cases Mk hwfr with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
    rcases ch3.cases_tail with heq | ⟨p, ch4, stp⟩
    · exfalso; rw [heq] at hv; omega
    · obtain ⟨⟨hrp, _⟩, hpright⟩ := stp
      have hpfr : clr Mk p = Color.free := hrp.2.1
      have hpm : p.1 = (m : ℤ) := by
        have hb := free_cases Mk hpfr
        rcases hrp.1 with ⟨hcol, hstep⟩ | ⟨hrow, hstep⟩ <;> omega
      have hpint : 0 ≤ p.1 ∧ p.1 ≤ (m : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (n : ℤ) := by
        rcases free_cases Mk hpfr with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
      refine ⟨(⟨w.1.toNat, by omega⟩, ⟨w.2.toNat, by omega⟩),
        (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩),
        free_interior Mk hwfr hwint.1 hwint.2.1 hwint.2.2.2,
        free_interior Mk hpfr hpint.1 hpint.2.1 hpint.2.2.2,
        ?_, ?_, rook_chain_toFin Mk ch4 hwint hpint⟩
      · exact Fin.ext (by simp; omega)
      · exact Fin.ext (by simp [Fin.last]; omega)

end Pipelines

end SteinhausWalk

/-- **Discrete Steinhaus/Hex crossing duality (general marking).**  On the board
`Fin (m+1) × Fin (n+1)`, for an arbitrary decidable marking: either the marked cells contain a
king-connected chain from the bottom row to the top row, or the free cells contain a
rook-connected chain from the left column to the right column.  Mechanism: pad the board with
sentinels (marked bottom/top rows, free left/right columns), walk the marked/free interface with
the right-hand rule from the pinned start dart, terminate by pigeonhole against predecessor
uniqueness, and read the crossing off the exit; the king/rook asymmetry enters at the diagonal
turn, which keeps the marked shore king-connected. -/
theorem discrete_crossing_duality {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop)
    [DecidablePred Mk] :
    (∃ a b : Fin (m + 1) × Fin (n + 1),
        Mk a ∧ Mk b ∧ a.2 = 0 ∧ b.2 = Fin.last n ∧ markReach Mk a b)
    ∨ (∃ a b : Fin (m + 1) × Fin (n + 1),
        ¬ Mk a ∧ ¬ Mk b ∧ a.1 = 0 ∧ b.1 = Fin.last m ∧ freeReach Mk a b) := by
  rcases SteinhausWalk.exit_classification Mk with h | h
  · exact Or.inl (SteinhausWalk.marked_pipeline Mk h)
  · exact Or.inr (SteinhausWalk.free_pipeline Mk h)

end RHTower

/-!
## Stage C — the continuous rectangle crossing duality

The compact clopen separation (Stage A) splits `K ∩ Rect` into a bottom family missing the top
edge and a top family missing the bottom edge, at three positive separation distances.  A grid of
mesh below an eighth of the least separation marks the cells meeting the split; a marked king
chain crossing bottom-to-top is impossible — king-adjacent cells are too close for the chain to
change family, and a single family cannot span its forbidden edge — so the discrete Steinhaus
duality produces a free rook chain crossing left-to-right, whose cell centres assemble into a
polygonal path through `Rect ∖ K`.
-/

namespace RHTower

namespace SteinhausWalk

open Relation Metric Set

/-- Convex-combination coordinate bound. -/
theorem comb_bounds {a b t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    min a b ≤ (1 - t) * a + t * b ∧ (1 - t) * a + t * b ≤ max a b := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    constructor <;> nlinarith
  · rw [min_eq_right hab, max_eq_left hab]
    constructor <;> nlinarith

/-- Coordinate bounds along a real segment in `ℂ`. -/
theorem segment_coord_bounds {p q z : ℂ} (hz : z ∈ segment ℝ p q) :
    (min p.re q.re ≤ z.re ∧ z.re ≤ max p.re q.re) ∧
      (min p.im q.im ≤ z.im ∧ z.im ≤ max p.im q.im) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hre : ((1 - t) • p + t • q).re = (1 - t) * p.re + t * q.re := by
    simp [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
  have him : ((1 - t) • p + t • q).im = (1 - t) * p.im + t * q.im := by
    simp [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
  rw [hre, him]
  exact ⟨comb_bounds ht.1 ht.2, comb_bounds ht.1 ht.2⟩

/-- A segment whose endpoints lie in an axis-aligned box stays in the box. -/
theorem segment_in_box {p q : ℂ} {rlo rhi ilo ihi : ℝ}
    (hp : rlo ≤ p.re ∧ p.re ≤ rhi ∧ ilo ≤ p.im ∧ p.im ≤ ihi)
    (hq : rlo ≤ q.re ∧ q.re ≤ rhi ∧ ilo ≤ q.im ∧ q.im ≤ ihi) :
    ∀ z ∈ segment ℝ p q, rlo ≤ z.re ∧ z.re ≤ rhi ∧ ilo ≤ z.im ∧ z.im ≤ ihi := by
  intro z hz
  obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := segment_coord_bounds hz
  refine ⟨le_trans (le_min hp.1 hq.1) hr1, le_trans hr2 (max_le hp.2.1 hq.2.1),
    le_trans (le_min hp.2.2.1 hq.2.2.1) hi1, le_trans hi2 (max_le hp.2.2.2 hq.2.2.2)⟩

/-- Positive uniform separation between a nonempty compact set and a disjoint nonempty closed
set. -/
theorem exists_uniform_separation {s t : Set ℂ} (hs : IsCompact s) (ht : IsClosed t)
    (hst : Disjoint s t) (hsne : s.Nonempty) (htne : t.Nonempty) :
    ∃ δ > 0, ∀ p ∈ s, ∀ q ∈ t, δ ≤ dist p q := by
  obtain ⟨p₀, hp₀, hmin⟩ :=
    hs.exists_isMinOn hsne (Metric.continuous_infDist_pt t).continuousOn
  refine ⟨Metric.infDist p₀ t, ?_, ?_⟩
  · rcases lt_or_eq_of_le (Metric.infDist_nonneg (x := p₀) (s := t)) with h | h
    · exact h
    · exfalso
      have : p₀ ∈ t := (ht.mem_iff_infDist_zero htne).mpr h.symm
      exact Set.disjoint_left.mp hst hp₀ this
  · intro p hp q hq
    exact le_trans (hmin hp) (Metric.infDist_le_dist_of_mem hq)

/-- Distance is bounded by the sum of coordinate distances. -/
theorem dist_le_coord {p q : ℂ} : dist p q ≤ |p.re - q.re| + |p.im - q.im| := by
  rw [Complex.dist_eq]
  calc ‖p - q‖ ≤ |(p - q).re| + |(p - q).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |p.re - q.re| + |p.im - q.im| := by rw [Complex.sub_re, Complex.sub_im]

end SteinhausWalk

end RHTower

namespace RHTower

open SteinhausWalk Metric Set

set_option maxHeartbeats 1600000 in
/-- **Stage C — rectangle crossing duality.**  For a closed set `K` and a closed rectangle
`[x₀,x₁] × [y₀,y₁]`: either `K` meets the rectangle in a connected *curtain* joining the bottom
edge to the top edge, or the rectangle carries a polygonal path from its left edge to its right
edge whose every segment avoids `K`.  Mechanism: the Stage-A compact clopen separation splits
`K ∩ Rect` into a bottom family missing the top edge and a top family missing the bottom edge; a
grid of mesh below an eighth of the least separation cannot support a marked king chain crossing
bottom-to-top (king-adjacent cells are too close for the chain to change family, and one family
cannot span its forbidden edge), so the discrete Steinhaus duality yields a free rook chain
crossing left-to-right, and its cell centres assemble into the polygonal path. -/
theorem rectangle_crossing_duality {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    {K : Set ℂ} (hK : IsClosed K) :
    (∃ C : Set ℂ,
        (∀ z ∈ C, z ∈ K ∧ x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁) ∧
        IsConnected C ∧ (∃ p ∈ C, p.im = y₀) ∧ (∃ p ∈ C, p.im = y₁))
    ∨ (∃ (N : ℕ) (v : Fin (N + 1) → ℂ),
        (∀ i : Fin N, ∀ z ∈ segment ℝ (v i.castSucc) (v i.succ),
          (x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁) ∧ z ∉ K) ∧
        (v 0).re = x₀ ∧ (v (Fin.last N)).re = x₁) := by
  classical
  by_cases hbr : ∃ C : Set ℂ,
      (∀ z ∈ C, z ∈ K ∧ x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁) ∧
      IsConnected C ∧ (∃ p ∈ C, p.im = y₀) ∧ (∃ p ∈ C, p.im = y₁)
  · exact Or.inl hbr
  refine Or.inr ?_
  -- the rectangle and the two horizontal edge lines
  set Rect : Set ℂ := {z : ℂ | x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁} with hRect
  have hRectC : IsCompact Rect := by
    have he : Rect = Complex.reProdIm (Set.Icc x₀ x₁) (Set.Icc y₀ y₁) := by
      ext z
      simp only [hRect, Set.mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc]
      tauto
    rw [he]
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hKC : IsCompact (K ∩ Rect) := hRectC.inter_left hK
  set Abot : Set ℂ := {z : ℂ | z.im = y₀} with hAbot
  set Btop : Set ℂ := {z : ℂ | z.im = y₁} with hBtop
  have hAcl : IsClosed Abot := isClosed_eq Complex.continuous_im continuous_const
  have hBcl : IsClosed Btop := isClosed_eq Complex.continuous_im continuous_const
  -- Stage A input: no connected curtain
  have hnc : ∀ C ⊆ K ∩ Rect, IsConnected C →
      ¬((C ∩ Abot).Nonempty ∧ (C ∩ Btop).Nonempty) := by
    rintro C hC hconn ⟨⟨p, hpC, hpA⟩, ⟨q, hqC, hqB⟩⟩
    refine hbr ⟨C, ?_, hconn, ⟨p, hpC, hpA⟩, ⟨q, hqC, hqB⟩⟩
    intro z hz
    obtain ⟨hzK, hzR⟩ := hC hz
    exact ⟨hzK, hzR.1, hzR.2.1, hzR.2.2.1, hzR.2.2.2⟩
  obtain ⟨K₁, K₂, hunion, hK₁c, hK₂c, hdisj, hK₁B, hK₂A⟩ :=
    compact_separation_of_no_joining_component hKC hAcl hBcl hnc
  -- single-segment path along a K-free horizontal line
  have mkline : ∀ yc : ℝ, y₀ ≤ yc → yc ≤ y₁ →
      (∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → z.im = yc → z ∉ K) →
      ∃ (N : ℕ) (v : Fin (N + 1) → ℂ),
        (∀ i : Fin N, ∀ z ∈ segment ℝ (v i.castSucc) (v i.succ),
          (x₀ ≤ z.re ∧ z.re ≤ x₁ ∧ y₀ ≤ z.im ∧ z.im ≤ y₁) ∧ z ∉ K) ∧
        (v 0).re = x₀ ∧ (v (Fin.last N)).re = x₁ := by
    intro yc hyc1 hyc2 hno
    refine ⟨1, ![⟨x₀, yc⟩, ⟨x₁, yc⟩], ?_, ?_, ?_⟩
    · intro i z hz
      have hi : i = 0 := Fin.ext (by omega)
      subst hi
      have hz' : z ∈ segment ℝ (⟨x₀, yc⟩ : ℂ) (⟨x₁, yc⟩ : ℂ) := by
        simpa using hz
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := segment_coord_bounds hz'
      simp only [min_self, max_self] at hi1 hi2
      have hzim : z.im = yc := le_antisymm hi2 hi1
      have hre1 : x₀ ≤ z.re := le_trans (le_min le_rfl hx.le) hr1
      have hre2 : z.re ≤ x₁ := le_trans hr2 (max_le hx.le le_rfl)
      exact ⟨⟨hre1, hre2, hzim ▸ hyc1, hzim ▸ hyc2⟩, hno z hre1 hre2 hzim⟩
    · simp
    · simp [show Fin.last 1 = 1 from rfl]
  -- degenerate families: a single horizontal segment suffices
  by_cases hK1e : K₁ = ∅
  · refine mkline y₀ le_rfl hy.le ?_
    intro z hzr1 hzr2 hzim hzK
    have hzR : z ∈ Rect := by
      rw [hRect]
      exact ⟨hzr1, hzr2, by rw [hzim], by rw [hzim]; exact hy.le⟩
    have hz12 : z ∈ K₁ ∪ K₂ := by rw [← hunion]; exact ⟨hzK, hzR⟩
    rcases hz12 with h | h
    · rw [hK1e] at h; exact h
    · have : z ∈ K₂ ∩ Abot := ⟨h, hzim⟩
      rw [hK₂A] at this
      exact this
  by_cases hK2e : K₂ = ∅
  · refine mkline y₁ hy.le le_rfl ?_
    intro z hzr1 hzr2 hzim hzK
    have hzR : z ∈ Rect := by
      rw [hRect]
      exact ⟨hzr1, hzr2, by rw [hzim]; exact hy.le, by rw [hzim]⟩
    have hz12 : z ∈ K₁ ∪ K₂ := by rw [← hunion]; exact ⟨hzK, hzR⟩
    rcases hz12 with h | h
    · have : z ∈ K₁ ∩ Btop := ⟨h, hzim⟩
      rw [hK₁B] at this
      exact this
    · rw [hK2e] at h; exact h
  have hK1ne : K₁.Nonempty := Set.nonempty_iff_ne_empty.mpr hK1e
  have hK2ne : K₂.Nonempty := Set.nonempty_iff_ne_empty.mpr hK2e
  -- the three positive separations and the least of them
  obtain ⟨δ₁, hδ₁p, hδ₁⟩ :=
    exists_uniform_separation hK₁c hK₂c.isClosed hdisj hK1ne hK2ne
  obtain ⟨δ₂, hδ₂p, hδ₂⟩ :=
    exists_uniform_separation hK₁c hBcl
      (Set.disjoint_iff_inter_eq_empty.mpr hK₁B) hK1ne ⟨⟨x₀, y₁⟩, rfl⟩
  obtain ⟨δ₃, hδ₃p, hδ₃⟩ :=
    exists_uniform_separation hK₂c hAcl
      (Set.disjoint_iff_inter_eq_empty.mpr hK₂A) hK2ne ⟨⟨x₀, y₀⟩, rfl⟩
  set δ : ℝ := min δ₁ (min δ₂ δ₃) with hδdef
  have hδp : 0 < δ := lt_min hδ₁p (lt_min hδ₂p hδ₃p)
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδ2 : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ δ₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- mesh
  obtain ⟨M, hM⟩ := exists_nat_gt (max (x₁ - x₀) (y₁ - y₀) / (δ / 8))
  have hd8 : (0 : ℝ) < δ / 8 := by positivity
  have hmesh : ∀ w : ℝ, w ≤ max (x₁ - x₀) (y₁ - y₀) → w / (M + 1) < δ / 8 := by
    intro w hw
    rw [div_lt_iff₀ (by positivity)]
    calc w ≤ max (x₁ - x₀) (y₁ - y₀) := hw
      _ = max (x₁ - x₀) (y₁ - y₀) / (δ / 8) * (δ / 8) := by field_simp
      _ < M * (δ / 8) := by
          exact mul_lt_mul_of_pos_right hM hd8
      _ ≤ δ / 8 * (M + 1) := by nlinarith [hd8.le]
  set wx : ℝ := (x₁ - x₀) / (M + 1) with hwxdef
  set wy : ℝ := (y₁ - y₀) / (M + 1) with hwydef
  have hwxp : 0 < wx := div_pos (by linarith) (by positivity)
  have hwyp : 0 < wy := div_pos (by linarith) (by positivity)
  have hwx8 : wx < δ / 8 := hmesh _ (le_max_left _ _)
  have hwy8 : wy < δ / 8 := hmesh _ (le_max_right _ _)
  have hwxs : ((M : ℝ) + 1) * wx = x₁ - x₀ := by
    rw [hwxdef]; field_simp
  have hwys : ((M : ℝ) + 1) * wy = y₁ - y₀ := by
    rw [hwydef]; field_simp
  -- cells, centres, marking
  set cell : Fin (M + 1) × Fin (M + 1) → Set ℂ := fun c =>
    {z : ℂ | x₀ + (c.1.val : ℝ) * wx ≤ z.re ∧ z.re ≤ x₀ + ((c.1.val : ℝ) + 1) * wx ∧
             y₀ + (c.2.val : ℝ) * wy ≤ z.im ∧ z.im ≤ y₀ + ((c.2.val : ℝ) + 1) * wy}
    with hcelldef
  have hcellRect : ∀ c, cell c ⊆ Rect := by
    intro c z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hc1 : ((c.1.val : ℝ) + 1) ≤ (M : ℝ) + 1 := by
      have := c.1.is_le
      exact_mod_cast Nat.succ_le_succ this
    have hc2 : ((c.2.val : ℝ) + 1) ≤ (M : ℝ) + 1 := by
      have := c.2.is_le
      exact_mod_cast Nat.succ_le_succ this
    rw [hRect]
    have hb1 : (0 : ℝ) ≤ (c.1.val : ℝ) * wx := mul_nonneg (Nat.cast_nonneg _) hwxp.le
    have hb2 : ((c.1.val : ℝ) + 1) * wx ≤ ((M : ℝ) + 1) * wx :=
      mul_le_mul_of_nonneg_right hc1 hwxp.le
    have hb3 : (0 : ℝ) ≤ (c.2.val : ℝ) * wy := mul_nonneg (Nat.cast_nonneg _) hwyp.le
    have hb4 : ((c.2.val : ℝ) + 1) * wy ≤ ((M : ℝ) + 1) * wy :=
      mul_le_mul_of_nonneg_right hc2 hwyp.le
    exact ⟨by linarith, by linarith [hwxs], by linarith, by linarith [hwys]⟩
  set Mk : Fin (M + 1) × Fin (M + 1) → Prop := fun c =>
    ((cell c) ∩ (K₁ ∪ K₂)).Nonempty with hMkdef
  letI : DecidablePred Mk := Classical.decPred _
  rcases discrete_crossing_duality Mk with
    ⟨a, b, hMa, hMb, ha2, hb2, hreach⟩ | ⟨a, b, hFa, hFb, ha1, hb1, hreach⟩
  · -- a marked king chain bottom-to-top is impossible
    exfalso
    have hclose : ∀ {c c' : Fin (M + 1) × Fin (M + 1)}, kingAdj c c' →
        ∀ p ∈ cell c, ∀ q ∈ cell c', dist p q < δ := by
      intro c c' hadj p hp q hq
      obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩, _⟩ := hadj
      have hk1 : (c.1.val : ℝ) ≤ (c'.1.val : ℝ) + 1 := by exact_mod_cast k1
      have hk2 : (c'.1.val : ℝ) ≤ (c.1.val : ℝ) + 1 := by exact_mod_cast k2
      have hk3 : (c.2.val : ℝ) ≤ (c'.2.val : ℝ) + 1 := by exact_mod_cast k3
      have hk4 : (c'.2.val : ℝ) ≤ (c.2.val : ℝ) + 1 := by exact_mod_cast k4
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
      have hre : |p.re - q.re| ≤ 2 * wx := by
        rw [abs_le]
        constructor <;> nlinarith [hwxp.le]
      have him : |p.im - q.im| ≤ 2 * wy := by
        rw [abs_le]
        constructor <;> nlinarith [hwyp.le]
      calc dist p q ≤ |p.re - q.re| + |p.im - q.im| := dist_le_coord
        _ ≤ 2 * wx + 2 * wy := add_le_add hre him
        _ < δ := by linarith
    have hmono : ∀ {c c' : Fin (M + 1) × Fin (M + 1)}, kingStep Mk c c' →
        ((cell c) ∩ K₁).Nonempty → ((cell c') ∩ K₁).Nonempty := by
      rintro c c' ⟨hadj, _, hMc'⟩ ⟨p, hp, hpK₁⟩
      obtain ⟨q, hq, hqK⟩ := hMc'
      rcases hqK with hqK₁ | hqK₂
      · exact ⟨q, hq, hqK₁⟩
      · exact absurd (hδ₁ p hpK₁ q hqK₂) (not_le.mpr (lt_of_lt_of_le (hclose hadj p hp q hq) hδ1))
    have hchain : ∀ {c}, markReach Mk a c →
        ((cell a) ∩ K₁).Nonempty → ((cell c) ∩ K₁).Nonempty := by
      intro c h
      induction h with
      | refl => exact id
      | tail h' step ih => intro h0; exact hmono step (ih h0)
    obtain ⟨p, hp, hpK⟩ := hMa
    rcases hpK with hpK₁ | hpK₂
    · -- the bottom family would reach the top edge
      obtain ⟨q, hq, hqK₁⟩ := hchain hreach ⟨p, hp, hpK₁⟩
      have hb2v : ((b.2.val : ℝ)) = (M : ℝ) := by rw [hb2]; simp
      obtain ⟨_, _, hq3, hq4⟩ := hq
      rw [hb2v] at hq3 hq4
      have hqB : δ₂ ≤ dist q (⟨q.re, y₁⟩ : ℂ) := hδ₂ q hqK₁ _ rfl
      have hqd : dist q (⟨q.re, y₁⟩ : ℂ) ≤ wy := by
        calc dist q _ ≤ |q.re - q.re| + |q.im - y₁| := dist_le_coord
          _ = |q.im - y₁| := by simp
          _ ≤ wy := by rw [abs_le]; constructor <;> nlinarith [hwys]
      linarith [hδ2]
    · -- the top family would reach the bottom edge
      have ha2v : ((a.2.val : ℝ)) = 0 := by rw [ha2]; simp
      obtain ⟨_, _, hp3, hp4⟩ := hp
      rw [ha2v] at hp3 hp4
      have hpA : δ₃ ≤ dist p (⟨p.re, y₀⟩ : ℂ) := hδ₃ p hpK₂ _ rfl
      have hpd : dist p (⟨p.re, y₀⟩ : ℂ) ≤ wy := by
        calc dist p _ ≤ |p.re - p.re| + |p.im - y₀| := dist_le_coord
          _ = |p.im - y₀| := by simp
          _ ≤ wy := by rw [abs_le]; constructor <;> nlinarith
      linarith [hδ3]
  · -- the free rook chain assembles into the polygonal path
    have hfreecell : ∀ {c}, ¬ Mk c → ∀ z ∈ cell c, z ∉ K := by
      intro c hc z hz hzK
      exact hc ⟨z, hz, by rw [← hunion]; exact ⟨hzK, hcellRect c hz⟩⟩
    set ctr : Fin (M + 1) × Fin (M + 1) → ℂ := fun c =>
      ⟨x₀ + (c.1.val : ℝ) * wx + wx / 2, y₀ + (c.2.val : ℝ) * wy + wy / 2⟩ with hctrdef
    have hctrre : ∀ c, (ctr c).re = x₀ + (c.1.val : ℝ) * wx + wx / 2 := fun c => by
      rw [hctrdef]
    have hctrim : ∀ c, (ctr c).im = y₀ + (c.2.val : ℝ) * wy + wy / 2 := fun c => by
      rw [hctrdef]
    have hctrmem : ∀ c, ctr c ∈ cell c := by
      intro c
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hctrre]; linarith [hwxp.le]
      · rw [hctrre]; linarith [hwxp.le]
      · rw [hctrim]; linarith [hwyp.le]
      · rw [hctrim]; linarith [hwyp.le]
    -- a segment between centres of vertically adjacent cells stays in their union
    have hsegV : ∀ (i j j' : Fin (M + 1)), j.val + 1 = j'.val →
        ∀ z ∈ segment ℝ (ctr (i, j)) (ctr (i, j')), z ∈ cell (i, j) ∪ cell (i, j') := by
      intro i j j' hjj z hz
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := segment_coord_bounds hz
      have hjr : (j'.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast hjj.symm
      simp only [hctrre] at hr1 hr2
      simp only [hctrim] at hi1 hi2
      simp only [hjr] at hi1 hi2
      simp only [min_self, max_self] at hr1 hr2
      have hre : z.re = x₀ + (i.val : ℝ) * wx + wx / 2 := le_antisymm hr2 hr1
      have him1 : y₀ + (j.val : ℝ) * wy + wy / 2 ≤ z.im :=
        le_trans (le_min le_rfl (by linarith [hwyp.le])) hi1
      have him2 : z.im ≤ y₀ + ((j.val : ℝ) + 1) * wy + wy / 2 :=
        le_trans hi2 (max_le (by linarith [hwyp.le]) le_rfl)
      by_cases hsplit : z.im ≤ y₀ + ((j.val : ℝ) + 1) * wy
      · exact Or.inl ⟨by rw [hre]; linarith [hwxp.le], by rw [hre]; linarith,
          by linarith [hwyp.le], hsplit⟩
      · refine Or.inr ⟨by rw [hre]; linarith [hwxp.le], by rw [hre]; linarith, ?_, ?_⟩
        · show y₀ + (j'.val : ℝ) * wy ≤ z.im
          rw [hjr]; linarith
        · show z.im ≤ y₀ + ((j'.val : ℝ) + 1) * wy
          rw [hjr]; linarith [hwyp.le]
    -- and horizontally adjacent cells, mirrored
    have hsegH : ∀ (i i' j : Fin (M + 1)), i.val + 1 = i'.val →
        ∀ z ∈ segment ℝ (ctr (i, j)) (ctr (i', j)), z ∈ cell (i, j) ∪ cell (i', j) := by
      intro i i' j hii z hz
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := segment_coord_bounds hz
      have hir : (i'.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hii.symm
      simp only [hctrim] at hi1 hi2
      simp only [hctrre] at hr1 hr2
      simp only [hir] at hr1 hr2
      simp only [min_self, max_self] at hi1 hi2
      have him : z.im = y₀ + (j.val : ℝ) * wy + wy / 2 := le_antisymm hi2 hi1
      have hre1 : x₀ + (i.val : ℝ) * wx + wx / 2 ≤ z.re :=
        le_trans (le_min le_rfl (by linarith [hwxp.le])) hr1
      have hre2 : z.re ≤ x₀ + ((i.val : ℝ) + 1) * wx + wx / 2 :=
        le_trans hr2 (max_le (by linarith [hwxp.le]) le_rfl)
      by_cases hsplit : z.re ≤ x₀ + ((i.val : ℝ) + 1) * wx
      · exact Or.inl ⟨by linarith [hwxp.le], hsplit, by rw [him]; linarith [hwyp.le],
          by rw [him]; linarith⟩
      · refine Or.inr ⟨?_, ?_, by rw [him]; linarith [hwyp.le], by rw [him]; linarith⟩
        · show x₀ + (i'.val : ℝ) * wx ≤ z.re
          rw [hir]; linarith
        · show z.re ≤ x₀ + ((i'.val : ℝ) + 1) * wx
          rw [hir]; linarith [hwxp.le]
    -- segments between centres of rook-adjacent free cells are admissible
    have hseg : ∀ {c c'}, rookStep Mk c c' →
        ∀ z ∈ segment ℝ (ctr c) (ctr c'), z ∈ Rect ∧ z ∉ K := by
      rintro c c' ⟨hadj, hfc, hfc'⟩ z hz
      have hcup : z ∈ cell c ∪ cell c' := by
        obtain ⟨ci, cj⟩ := c
        obtain ⟨ci', cj'⟩ := c'
        rcases hadj with ⟨hcol, hstep⟩ | ⟨hrow, hstep⟩
        · simp only at hcol
          subst hcol
          rcases hstep with h | h
          · exact hsegV ci cj cj' h z hz
          · have := hsegV ci cj' cj h z (by rwa [segment_symm])
            rwa [Set.union_comm] at this
        · simp only at hrow
          subst hrow
          rcases hstep with h | h
          · exact hsegH ci ci' cj h z hz
          · have := hsegH ci' ci cj h z (by rwa [segment_symm])
            rwa [Set.union_comm] at this
      rcases hcup with h | h
      · exact ⟨hcellRect c h, hfreecell hfc z h⟩
      · exact ⟨hcellRect c' h, hfreecell hfc' z h⟩
    -- assemble the polygonal path along the chain
    have ha1v : ((a.1.val : ℝ)) = 0 := by rw [ha1]; simp
    set lp : ℂ := ⟨x₀, y₀ + (a.2.val : ℝ) * wy + wy / 2⟩ with hlpdef
    have hlpre : lp.re = x₀ := by rw [hlpdef]
    have hlpim : lp.im = y₀ + (a.2.val : ℝ) * wy + wy / 2 := by rw [hlpdef]
    have hlpmem : lp ∈ cell a := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlpre, ha1v]; norm_num
      · rw [hlpre, ha1v]; norm_num; linarith [hwxp.le]
      · rw [hlpim]; linarith [hwyp.le]
      · rw [hlpim]; linarith [hwyp.le]
    have builder : ∀ {c}, Relation.ReflTransGen (rookStep Mk) a c →
        ∃ (N : ℕ) (v : Fin (N + 1) → ℂ),
          (∀ i : Fin N, ∀ z ∈ segment ℝ (v i.castSucc) (v i.succ), z ∈ Rect ∧ z ∉ K) ∧
          v 0 = lp ∧ v (Fin.last N) = ctr c := by
      intro c h
      induction h with
      | refl =>
        refine ⟨1, ![lp, ctr a], ?_, by simp, by simp [show Fin.last 1 = 1 from rfl]⟩
        intro i z hz
        have hi : i = 0 := Fin.ext (by omega)
        subst hi
        have hz' : z ∈ segment ℝ lp (ctr a) := by simpa using hz
        have hbox := segment_in_box
          ⟨hlpmem.1, hlpmem.2.1, hlpmem.2.2.1, hlpmem.2.2.2⟩
          ⟨(hctrmem a).1, (hctrmem a).2.1, (hctrmem a).2.2.1, (hctrmem a).2.2.2⟩ z hz'
        have hzc : z ∈ cell a := ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩
        exact ⟨hcellRect a hzc, hfreecell hFa z hzc⟩
      | @tail q c h' step ih =>
        obtain ⟨N, v, hvseg, hv0, hvlast⟩ := ih
        refine ⟨N + 1, Fin.snoc v (ctr c), ?_, ?_, ?_⟩
        · intro i z hz
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · have e1 : (Fin.snoc v (ctr c) : Fin (N + 2) → ℂ) (j.castSucc).castSucc = v j.castSucc := by
              rw [Fin.snoc_castSucc]
            have e2 : (Fin.snoc v (ctr c) : Fin (N + 2) → ℂ) (j.castSucc).succ = v j.succ := by
              have hidx : (j.castSucc).succ = (j.succ).castSucc := by
                ext
                simp
              rw [hidx, Fin.snoc_castSucc]
            rw [e1, e2] at hz
            exact hvseg j z hz
          · have e1 : (Fin.snoc v (ctr c) : Fin (N + 2) → ℂ) (Fin.last N).castSucc = v (Fin.last N) := by
              simp
            have e2 : (Fin.snoc v (ctr c) : Fin (N + 2) → ℂ) (Fin.last N).succ = ctr c := by
              rw [Fin.succ_last]
              simp
            rw [e1, e2, hvlast] at hz
            exact hseg step z hz
        · rw [show (0 : Fin (N + 2)) = Fin.castSucc 0 from (Fin.castSucc_zero).symm,
            Fin.snoc_castSucc]
          exact hv0
        · exact Fin.snoc_last _ _
    obtain ⟨N, v, hvseg, hv0, hvlast⟩ := builder hreach
    have hb1v : ((b.1.val : ℝ)) = (M : ℝ) := by rw [hb1]; simp
    set rp : ℂ := ⟨x₁, y₀ + (b.2.val : ℝ) * wy + wy / 2⟩ with hrpdef
    have hrpre : rp.re = x₁ := by rw [hrpdef]
    have hrpim : rp.im = y₀ + (b.2.val : ℝ) * wy + wy / 2 := by rw [hrpdef]
    have hrpmem : rp ∈ cell b := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hrpre, hb1v]; linarith [hwxs, hwxp.le]
      · rw [hrpre, hb1v]; linarith [hwxs]
      · rw [hrpim]; linarith [hwyp.le]
      · rw [hrpim]; linarith [hwyp.le]
    refine ⟨N + 1, Fin.snoc v rp, ?_, ?_, ?_⟩
    · intro i z hz
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have e1 : (Fin.snoc v rp : Fin (N + 2) → ℂ) (j.castSucc).castSucc = v j.castSucc := by
          rw [Fin.snoc_castSucc]
        have e2 : (Fin.snoc v rp : Fin (N + 2) → ℂ) (j.castSucc).succ = v j.succ := by
          have hidx : (j.castSucc).succ = (j.succ).castSucc := by
            ext
            simp
          rw [hidx, Fin.snoc_castSucc]
        rw [e1, e2] at hz
        obtain ⟨hzR, hzK⟩ := hvseg j z hz
        rw [hRect] at hzR
        exact ⟨hzR, hzK⟩
      · have e1 : (Fin.snoc v rp : Fin (N + 2) → ℂ) (Fin.last N).castSucc = v (Fin.last N) := by
          simp
        have e2 : (Fin.snoc v rp : Fin (N + 2) → ℂ) (Fin.last N).succ = rp := by
          rw [Fin.succ_last]
          simp
        rw [e1, e2, hvlast] at hz
        have hbox := segment_in_box
          ⟨(hctrmem b).1, (hctrmem b).2.1, (hctrmem b).2.2.1, (hctrmem b).2.2.2⟩
          ⟨hrpmem.1, hrpmem.2.1, hrpmem.2.2.1, hrpmem.2.2.2⟩ z hz
        have hzc : z ∈ cell b := ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩
        have hzR := hcellRect b hzc
        rw [hRect] at hzR
        exact ⟨hzR, hfreecell hFb z hzc⟩
    · rw [show (0 : Fin (N + 2)) = Fin.castSucc 0 from (Fin.castSucc_zero).symm,
        Fin.snoc_castSucc, hv0]
    · rw [Fin.snoc_last]

end RHTower
