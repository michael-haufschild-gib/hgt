import GaloisForLFunctions.HTGeometry.GaussBonnetPolyhedralModels

/-!
# The flat torus as a closed triangulated surface

The Möbius torus is the seven-vertex triangulation of the two-torus: the vertices are `ℤ/7`, and
the fourteen faces are

```text
A_i = (i, i+1, i+3),      B_i = (i, i+2, i+3),      i ∈ ℤ/7.
```

Its twenty-one edges are the pairs at cyclic distance `1`, `2` and `3`, each carried by exactly two
triangle sides, so this is a genuine closed triangulated surface with

```text
χ = V - E + F = 7 - 21 + 14 = 0.
```

It is the quotient of the equilateral triangular lattice, so every face is realized isometrically
by the unit equilateral triangle, and the Gauss--Bonnet theorem of `GaussBonnetPolyhedral` gives
total angular defect `0`: the seven-vertex torus is flat.

Together with the tetrahedron of `GaussBonnetPolyhedralModels` this shows that the polyhedral
Gauss--Bonnet theorem is not restricted to the sphere: it computes the correct Euler characteristic
for surfaces of different genus.
-/

open Finset
open scoped Real

set_option maxRecDepth 40000

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- The fourteen faces of the Möbius torus, indexed by a parity bit and a residue mod `7`. -/
def torusCorner : Fin 2 × Fin 7 → Fin 3 → Fin 7 :=
  fun p j => if p.1 = 0 then ![p.2, p.2 + 1, p.2 + 3] j else ![p.2, p.2 + 2, p.2 + 3] j

/-- The Möbius torus: the seven-vertex triangulation of the two-torus, with every face realized by
the unit equilateral triangle. -/
noncomputable def triangulatedTorus : ClosedTriangulation (Fin 7) (Fin 2 × Fin 7) :=
  ClosedTriangulation.ofRealization (W := ℂ) (P := ℂ) torusCorner (fun _ => equilateralPoint)
    (fun _ => by simp [equilateralPoint])
    (by decide)

theorem triangulatedTorus_edges_card : triangulatedTorus.edges.card = 21 := by decide

theorem triangulatedTorus_eulerChar : triangulatedTorus.eulerChar = 0 := by
  unfold ClosedTriangulation.eulerChar
  rw [triangulatedTorus_edges_card]
  simp

/-- **Gauss--Bonnet for the seven-vertex torus.**  Its total angular defect is `0 = 2π·χ(T²)`. -/
theorem triangulatedTorus_totalDefect : triangulatedTorus.totalDefect = 0 := by
  rw [ClosedTriangulation.gauss_bonnet_polyhedral, triangulatedTorus_eulerChar]
  simp

end GaloisForLFunctions.HTGeometry.GaussBonnet
