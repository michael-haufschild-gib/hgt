import Mathlib

/-!
# Global Gauss--Bonnet for closed triangulated surfaces

A **closed triangulated surface** is a finite family of triangles glued along their sides so that
every edge belongs to exactly two triangle sides, each triangle carrying a Euclidean angle
assignment (its three angles sum to `π`).  This is the piecewise-flat -- "Euclidean cone" --
category of surfaces: the metric is flat on every face and on every edge, and all curvature is
concentrated at the vertices, where it is measured by the **angular defect**

```text
defect(v) = 2π - Σ (angles of the corners at v).
```

The Gauss--Bonnet theorem in this category is Descartes' theorem in its general form:

```text
Σ_{v} defect(v) = 2π · χ,      χ = V - E + F.
```

It is proved here from the two structural facts of a closed triangulated surface: every face has
three corners whose angles sum to `π`, and every edge carries exactly two sides, so `3F = 2E`.

The statement is completely unconditional: `χ` is the honest Euler characteristic computed from the
triangulation, the angular defects are the honest curvature, and the surface may have any genus.
-/

open scoped Real
open Finset

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

variable {V F : Type*}

/-- The vertex pair spanned by side `i` of triangle `f`. -/
def sideEdge [DecidableEq V] (corner : F → Fin 3 → V) (s : F × Fin 3) : Finset V :=
  {corner s.1 s.2, corner s.1 (s.2 + 1)}

/-- The set of edges of a triangulated surface: the vertex pairs spanned by its triangle sides. -/
def edgeSet [DecidableEq V] [Fintype F] (corner : F → Fin 3 → V) : Finset (Finset V) :=
  Finset.univ.image (sideEdge corner)

/-- A **closed triangulated surface** with a Euclidean angle structure: finitely many triangles,
each carrying angles summing to `π`, glued so that every edge lies on exactly two triangle
sides. -/
structure ClosedTriangulation (V F : Type*) [DecidableEq V] [Fintype V] [Fintype F] where
  /-- The three vertices of each triangle, cyclically ordered. -/
  corner : F → Fin 3 → V
  /-- The interior angle at each corner. -/
  angle : F → Fin 3 → ℝ
  /-- Every face is a Euclidean triangle: its angles sum to `π`. -/
  angleSum : ∀ f, ∑ i, angle f i = π
  /-- The surface is closed: every edge lies on exactly two triangle sides. -/
  edgeIncidence : ∀ e ∈ edgeSet corner,
    #{s ∈ (Finset.univ : Finset (F × Fin 3)) | sideEdge corner s = e} = 2

namespace ClosedTriangulation

variable [DecidableEq V] [Fintype V] [Fintype F] (T : ClosedTriangulation V F)

/-- The edges of the triangulation. -/
def edges : Finset (Finset V) := edgeSet T.corner

/-- The **Euler characteristic** `V - E + F` of the triangulation. -/
def eulerChar : ℤ := (Fintype.card V : ℤ) - (T.edges.card : ℤ) + (Fintype.card F : ℤ)

/-- The **angular defect** at a vertex: `2π` minus the total angle of the corners meeting there.
This is the concentrated Gaussian curvature of the piecewise-flat metric. -/
noncomputable def defect (v : V) : ℝ :=
  2 * π - ∑ s ∈ {s ∈ (Finset.univ : Finset (F × Fin 3)) | T.corner s.1 s.2 = v}, T.angle s.1 s.2

/-- The **total curvature** of the surface: the sum of all angular defects. -/
noncomputable def totalDefect : ℝ := ∑ v, T.defect v

/-- **Every edge carries two sides**, so `3F = 2E`. -/
theorem three_mul_card_face : 3 * Fintype.card F = 2 * T.edges.card := by
  have hmaps : Set.MapsTo (sideEdge T.corner) (↑(Finset.univ : Finset (F × Fin 3))) ↑T.edges := by
    intro s _
    simp only [edges, edgeSet, Finset.coe_image, Set.mem_image, Finset.coe_univ]
    exact ⟨s, trivial, rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∑ e ∈ T.edges,
      #{s ∈ (Finset.univ : Finset (F × Fin 3)) | sideEdge T.corner s = e} = 2 * T.edges.card := by
    have hall : ∀ e ∈ T.edges,
        #{s ∈ (Finset.univ : Finset (F × Fin 3)) | sideEdge T.corner s = e} = 2 :=
      fun e he => T.edgeIncidence e he
    rw [Finset.sum_congr rfl hall]
    simp [Finset.sum_const, mul_comm]
  have hleft : (Finset.univ : Finset (F × Fin 3)).card = 3 * Fintype.card F := by
    simp [Finset.card_univ, Fintype.card_prod, mul_comm]
  omega

/-- **Double counting the corners.**  Summing the corner angles vertex by vertex is summing them
face by face. -/
theorem sum_defect_angles :
    ∑ v : V, ∑ s ∈ {s ∈ (Finset.univ : Finset (F × Fin 3)) | T.corner s.1 s.2 = v},
        T.angle s.1 s.2
      = (Fintype.card F : ℝ) * π := by
  rw [Finset.sum_fiberwise_of_maps_to (fun s _ => Finset.mem_univ (T.corner s.1 s.2))
    (fun s : F × Fin 3 => T.angle s.1 s.2)]
  rw [Fintype.sum_prod_type]
  simp [T.angleSum, Finset.sum_const, mul_comm]

/-- **Gauss--Bonnet for closed triangulated surfaces (Descartes' theorem).**

```text
Σ_{v ∈ V} ( 2π - Σ angles at v )  =  2π ( V - E + F ).
```

The total angular defect of a closed piecewise-flat surface is `2π` times its Euler
characteristic. -/
theorem gauss_bonnet_polyhedral : T.totalDefect = 2 * π * (T.eulerChar : ℝ) := by
  have hE : 3 * Fintype.card F = 2 * T.edges.card := T.three_mul_card_face
  have hEr : 3 * (Fintype.card F : ℝ) = 2 * (T.edges.card : ℝ) := by exact_mod_cast hE
  have hsum := T.sum_defect_angles
  unfold totalDefect defect eulerChar
  rw [Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  linear_combination (-π) * hEr

end ClosedTriangulation

end GaloisForLFunctions.HTGeometry.GaussBonnet
