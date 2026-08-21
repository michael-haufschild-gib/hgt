import GaloisForLFunctions.HTGeometry.GaussBonnetModelSurfaces
import GaloisForLFunctions.HTGeometry.GaussBonnetTorus
import GaloisForLFunctions.HTGeometry.GaussBonnetWarpedPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetPolarPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetStarShaped
import GaloisForLFunctions.HTGeometry.GaussBonnetRiemann
import GaloisForLFunctions.HTGeometry.GaussBonnetPolygon
import GaloisForLFunctions.HTGeometry.GaussBonnetGlobalAssembly
import GaloisForLFunctions.HTGeometry.GaussBonnetTriangulatedTorus
import GaloisForLFunctions.HTGeometry.GaussBonnetGraph

/-!
# The Gauss--Bonnet theorem

This module is the capstone of the corpus' Gauss--Bonnet development.  It collects the
unconditional Lean statements proved in

* `GaussBonnetPlanarPartials` — planar partial derivatives and interval Fubini;
* `GaussBonnetOrthogonalPatch` — the local theorem on a coordinate rectangle;
* `GaussBonnetGeodesicPolar` — the local theorem for a geodesic disc on an arbitrary surface;
* `GaussBonnetGeodesicCurvature` — the intrinsic (covariant-derivative) geodesic curvature, and
  Liouville's formulas as theorems;
* `GaussBonnetPartialCalculus`, `GaussBonnetRiemann` — the Riemann curvature tensor of an
  orthogonal metric, and the theorem that the Gaussian curvature used here is the intrinsic
  sectional curvature;
* `GaussBonnetStarShaped` — the local theorem for an arbitrary star-shaped region on an arbitrary
  surface;
* `GaussBonnetRadialArc`, `GaussBonnetPolygon` — the arc identity, and the local theorem with
  corners for an arbitrary star-shaped geodesic polygon;
* `GaussBonnetPolarPatch`, `GaussBonnetWarpedPatch` — identification of the curvatures used there
  with the Gaussian curvature of the general orthogonal-coordinate formula;
* `GaussBonnetTorus` — the global theorem for doubly periodic metrics;
* `GaussBonnetWarped`, `GaussBonnetModelSurfaces` — the global theorem for surfaces of revolution,
  with the round sphere, the hyperbolic plane, the flat plane and the torus of revolution;
* `GaussBonnetPolyhedral`, `GaussBonnetPolyhedralModels`, `GaussBonnetTriangulatedTorus` — the
  global theorem for closed piecewise-flat surfaces of arbitrary genus, with the tetrahedron and
  the seven-vertex torus;
* `GaussBonnetGlobalAssembly` — the assembly law turning the local theorem on the faces of a closed
  surface into the global one;
* `GaussBonnetGraph` — the theorem for finite simple graphs.

Everything is stated in the same shape,

```text
∫∫ K dA + ∮ κ_g ds + Σ (exterior angles)  =  2π · χ,
```

with the curvature and the Euler characteristic of the relevant category.
-/

open scoped Real

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- **Gauss--Bonnet, local form.**  On every coordinate rectangle of every smooth orthogonal
Riemannian metric `E du² + G dv²`,

```text
∫∫_R K dA + ∮_{∂R} κ_g ds + 4·(π/2) = 2π = 2π·χ(disc).
```
-/
theorem gaussBonnet_local_rectangle (M : OrthogonalPatch) (a b c d : ℝ) :
    M.totalCurvature a b c d + M.boundaryTurning a b c d + 4 * (π / 2) = 2 * π :=
  M.gauss_bonnet_rectangle a b c d

/-- **Gauss--Bonnet, geodesic-disc form.**  On an arbitrary smooth Riemannian surface written in
geodesic polar coordinates,

```text
∫∫_{D_R} K dA + ∮_{∂D_R} κ_g ds = 2π = 2π·χ(disc).
```
-/
theorem gaussBonnet_geodesic_disc (C : GeodesicPolarChart) {R : ℝ} (hR : 0 < R)
    (hne : ∀ θ : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) R, C.f (r, θ) ≠ 0) :
    C.totalCurvature R + C.boundaryTurning R = 2 * π :=
  C.gauss_bonnet_geodesic_disc hR hne

/-- **Gauss--Bonnet on the round unit sphere.**  For every geodesic disc of radius below the
injectivity radius `π`, `∫∫ K dA + ∮ κ_g ds = 2π`, with `K ≡ 1`. -/
theorem gaussBonnet_sphere_disc {R : ℝ} (h0 : 0 < R) (hpi : R < π) :
    spherePolarChart.totalCurvature R + spherePolarChart.boundaryTurning R = 2 * π :=
  spherePolarChart_gauss_bonnet h0 hpi

/-- **Gauss--Bonnet on the hyperbolic plane.**  For every geodesic disc,
`∫∫ K dA + ∮ κ_g ds = 2π`, with `K ≡ -1`. -/
theorem gaussBonnet_hyperbolic_disc {R : ℝ} (h0 : 0 < R) :
    hyperbolicPolarChart.totalCurvature R + hyperbolicPolarChart.boundaryTurning R = 2 * π :=
  hyperbolicPolarChart_gauss_bonnet h0

/-- **Gauss--Bonnet, star-shaped form.**  For every closed star-shaped region about the pole of a
geodesic polar chart on an arbitrary smooth Riemannian surface,

```text
∫∫_D K dA + ∮_{∂D} κ_g ds = 2π = 2π·χ(disc).
```
-/
theorem gaussBonnet_star_shaped {C : GeodesicPolarChart} (S : StarCurve C) :
    S.totalCurvature + S.boundaryTurning = 2 * π :=
  S.gauss_bonnet_star

/-- **Liouville's formula is a theorem.**  The geodesic curvature of the coordinate curves of an
orthogonal patch, defined intrinsically by the covariant derivative, is `-E_v/(2E√G)` and
`G_u/(2G√E)`. -/
theorem liouville_uCurve (M : OrthogonalPatch) (p : ℝ × ℝ) :
    M.geodesicCurvature p 1 0 0 0 = -py M.E p / (2 * M.E p * M.vSpeed p) :=
  M.geodesicCurvature_uCurve p

/-- Liouville's formula for the other family of coordinate curves. -/
theorem liouville_vCurve (M : OrthogonalPatch) (p : ℝ × ℝ) :
    M.geodesicCurvature p 0 1 0 0 = px M.G p / (2 * M.G p * M.uSpeed p) :=
  M.geodesicCurvature_vCurve p

/-- **Gauss--Bonnet with corners.**  For every closed star-shaped polygon about the pole of a
geodesic polar chart on an arbitrary smooth Riemannian surface,

```text
∫∫_D K dA + ∮_{∂D} κ_g ds + Σ_i ε_i = 2π = 2π·χ(disc).
```
-/
theorem gaussBonnet_polygon {C : GeodesicPolarChart} (P : StarPolygon C) :
    P.totalCurvature + P.boundaryTurning + P.totalExteriorAngle = 2 * π :=
  P.gauss_bonnet_polygon

/-- **Both curvatures in the Gauss--Bonnet identity are intrinsic.**  The Gaussian curvature used
throughout is the sectional curvature `R₁₂₁₂/(EG)` of the Levi-Civita connection. -/
theorem gaussCurvature_eq_sectional (M : OrthogonalPatch) (u v : ℝ) :
    M.sectionalCurvature (u, v) = M.gaussCurvature (u, v) :=
  M.sectionalCurvature_eq_gaussCurvature u v

/-- **Gauss--Bonnet, global form on the torus.**  Every smooth doubly periodic orthogonal
Riemannian metric — a coordinate-orthogonal metric on `T²` — satisfies

```text
∫∫_{T²} K dA = 0 = 2π·χ(T²).
```
-/
theorem gaussBonnet_torus (M : OrthogonalPatch) {p q : ℝ}
    (hEu : ∀ u v, M.E (u + p, v) = M.E (u, v)) (hEv : ∀ u v, M.E (u, v + q) = M.E (u, v))
    (hGu : ∀ u v, M.G (u + p, v) = M.G (u, v)) (hGv : ∀ u v, M.G (u, v + q) = M.G (u, v))
    (a c : ℝ) :
    M.totalCurvature a (a + p) c (c + q) = 2 * π * 0 :=
  M.gauss_bonnet_torus hEu hEv hGu hGv a c

/-- **Gauss--Bonnet, global form for a closed surface of revolution of sphere type.**

```text
∫∫_M K dA = 4π = 2π·χ(S²).
```
-/
theorem gaussBonnet_sphere_type {W : WarpProfile} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0) (hpoleA : W.d1 a = 1) (hpoleB : W.d1 b = -1) :
    W.totalCurvature a b = 2 * π * 2 :=
  WarpProfile.gauss_bonnet_sphere_type hab hne hpoleA hpoleB

/-- **Gauss--Bonnet, global form for closed piecewise-flat surfaces of arbitrary genus.**

```text
Σ_{v} ( 2π - Σ angles at v ) = 2π·χ.
```
-/
theorem gaussBonnet_polyhedral {V F : Type*} [DecidableEq V] [Fintype V] [Fintype F]
    (T : ClosedTriangulation V F) : T.totalDefect = 2 * π * (T.eulerChar : ℝ) :=
  T.gauss_bonnet_polyhedral

/-- **Gauss--Bonnet, global assembly form.**  For a closed surface cut into Gauss--Bonnet faces
glued isometrically,

```text
Σ_f ∫∫_f K dA = 2π · χ,     χ = V - E + F.
```

The local Gauss--Bonnet identity on each face is a theorem (`gaussBonnet_polygon`), not an
assumption: `ofStarPolygons` discharges it. -/
theorem gaussBonnet_global {ι : Type*} [Fintype ι] (A : ClosedSurfaceAssembly ι) :
    ∑ f, A.curv f = 2 * π * (A.eulerChar : ℝ) :=
  A.gauss_bonnet_global

/-- **Gauss--Bonnet for finite simple graphs.**  The total combinatorial curvature is the Euler
characteristic. -/
theorem gaussBonnet_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ x : V, 2 * π * graphCurvature G x = 2 * π * graphEulerChar G :=
  gauss_bonnet_graph_two_pi G

end GaloisForLFunctions.HTGeometry.GaussBonnet
