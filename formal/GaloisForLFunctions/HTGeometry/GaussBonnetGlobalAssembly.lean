import GaloisForLFunctions.HTGeometry.GaussBonnetPolygon
import GaloisForLFunctions.HTGeometry.GaussBonnetTriangulatedTorus

/-!
# Global Gauss--Bonnet by assembly of local Gauss--Bonnet faces

A closed surface cut into finitely many discs carries, on every face, the *local* Gauss--Bonnet
identity

```text
∫∫_f K dA + ∮_{∂f} κ_g ds + Σ (exterior angles of f) = 2π,
```

which for a star-shaped geodesic polygon is the theorem `StarPolygon.gauss_bonnet_polygon`.  Two
purely global facts turn this into the classical statement:

* the boundary integrals cancel in pairs, because each edge is traversed once in each direction by
  the two faces meeting along it and the identification is an isometry — so
  `Σ_f ∮_{∂f} κ_g ds = 0`;
* the interior angles around each vertex fill out a full turn on a smooth surface, so
  `Σ_f Σ (interior angles of f) = 2π · V`;
* every edge carries two sides, so `Σ_f (number of sides of f) = 2E`.

Summing the local identity over the faces and substituting these three counts gives

```text
Σ_f ∫∫_f K dA = 2π ( V - E + F ) = 2π · χ.
```

That is `ClosedSurfaceAssembly.gauss_bonnet_global`.  The local identity is *not* assumed: the
constructor `ofStarPolygons` builds an assembly out of a family of star-shaped geodesic polygons,
discharging it with the local theorem.  What the structure records are exactly the gluing data —
which is what "the faces are glued isometrically into a closed surface" means.

The seven-vertex flat torus of `GaussBonnetTriangulatedTorus` is written out as an assembly at the
end, certifying that the hypotheses are not vacuous.
-/

open scoped Real BigOperators

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A closed surface assembled from finitely many Gauss--Bonnet faces. -/
structure ClosedSurfaceAssembly (ι : Type*) [Fintype ι] where
  /-- The curvature integral of each face. -/
  curv : ι → ℝ
  /-- The boundary geodesic-curvature integral of each face. -/
  turning : ι → ℝ
  /-- The number of sides of each face. -/
  sides : ι → ℕ
  /-- The sum of the interior angles of each face. -/
  angleSum : ι → ℝ
  /-- The number of edges of the surface. -/
  edgeCount : ℕ
  /-- The number of vertices of the surface. -/
  vertexCount : ℕ
  /-- **Local Gauss--Bonnet** on each face. -/
  localGB : ∀ f, curv f + turning f + ((sides f : ℝ) * π - angleSum f) = 2 * π
  /-- The boundary integrals cancel: the faces are glued isometrically. -/
  gluing : ∑ f, turning f = 0
  /-- Every edge carries exactly two sides: the surface is closed. -/
  sideCount : ∑ f, sides f = 2 * edgeCount
  /-- The angles around every vertex fill a full turn: the surface is smooth. -/
  vertexAngles : ∑ f, angleSum f = 2 * π * vertexCount

namespace ClosedSurfaceAssembly

variable {ι : Type*} [Fintype ι] (A : ClosedSurfaceAssembly ι)

/-- The **Euler characteristic** `V - E + F` of the assembled surface. -/
def eulerChar : ℤ := (A.vertexCount : ℤ) - (A.edgeCount : ℤ) + (Fintype.card ι : ℤ)

/-- **Global Gauss--Bonnet.**  The total curvature of a closed surface assembled from
Gauss--Bonnet faces is `2π` times its Euler characteristic. -/
theorem gauss_bonnet_global : ∑ f, A.curv f = 2 * π * (A.eulerChar : ℝ) := by
  have hsum : ∑ f, (A.curv f + A.turning f + ((A.sides f : ℝ) * π - A.angleSum f))
      = ∑ _f : ι, (2 * π) := Finset.sum_congr rfl fun f _ => A.localGB f
  have hexp : ∑ f, (A.curv f + A.turning f + ((A.sides f : ℝ) * π - A.angleSum f))
      = (∑ f, A.curv f) + (∑ f, A.turning f)
        + ((∑ f, (A.sides f : ℝ)) * π - ∑ f, A.angleSum f) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsides : (∑ f, (A.sides f : ℝ)) = 2 * (A.edgeCount : ℝ) := by
    have := A.sideCount
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rw [hexp, A.gluing, hsides, A.vertexAngles] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  unfold eulerChar
  push_cast
  linarith [hsum]

end ClosedSurfaceAssembly

/-- **An assembly out of star-shaped geodesic polygons.**  The local Gauss--Bonnet identity is
discharged by `StarPolygon.gauss_bonnet_polygon`; only the gluing data is recorded. -/
noncomputable def ofStarPolygons {ι : Type*} [Fintype ι] {C : ι → GeodesicPolarChart}
    (P : ∀ f, StarPolygon (C f)) (edgeCount vertexCount : ℕ)
    (gluing : ∑ f, (P f).boundaryTurning = 0)
    (sideCount : ∑ f, (P f).n = 2 * edgeCount)
    (vertexAngles :
      ∑ f, ∑ i ∈ Finset.range (P f).n, (P f).interiorAngle i = 2 * π * vertexCount) :
    ClosedSurfaceAssembly ι where
  curv := fun f => (P f).totalCurvature
  turning := fun f => (P f).boundaryTurning
  sides := fun f => (P f).n
  angleSum := fun f => ∑ i ∈ Finset.range (P f).n, (P f).interiorAngle i
  edgeCount := edgeCount
  vertexCount := vertexCount
  localGB := fun f => by
    have h := (P f).gauss_bonnet_polygon
    have hint : (∑ i ∈ Finset.range (P f).n, (P f).interiorAngle i)
        = ((P f).n : ℝ) * π - (P f).totalExteriorAngle := by
      unfold StarPolygon.interiorAngle StarPolygon.totalExteriorAngle
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, mul_comm]
    rw [hint]
    linarith [h]
  gluing := gluing
  sideCount := sideCount
  vertexAngles := vertexAngles

/-! ### The seven-vertex flat torus as an assembly -/

/-- The Möbius torus as a closed-surface assembly: fourteen flat equilateral faces, twenty-one
edges, seven vertices, every vertex surrounded by six corners of angle `π/3`. -/
noncomputable def flatTorusAssembly : ClosedSurfaceAssembly (Fin 2 × Fin 7) where
  curv := fun _ => 0
  turning := fun _ => 0
  sides := fun _ => 3
  angleSum := fun _ => π
  edgeCount := 21
  vertexCount := 7
  localGB := fun _ => by push_cast; ring
  gluing := by simp
  sideCount := by simp
  vertexAngles := by simp [Finset.sum_const]; ring

theorem flatTorusAssembly_eulerChar : flatTorusAssembly.eulerChar = 0 := by
  unfold ClosedSurfaceAssembly.eulerChar flatTorusAssembly
  simp

/-- **Global Gauss--Bonnet for the flat torus**, through the assembly law. -/
theorem flatTorusAssembly_gauss_bonnet :
    ∑ f, flatTorusAssembly.curv f = 2 * π * 0 := by
  rw [flatTorusAssembly.gauss_bonnet_global, flatTorusAssembly_eulerChar]
  simp

end GaloisForLFunctions.HTGeometry.GaussBonnet
