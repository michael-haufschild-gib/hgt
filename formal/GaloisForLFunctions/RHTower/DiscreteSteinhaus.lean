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

end SteinhausWalk

end RHTower
