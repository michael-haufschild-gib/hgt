import GaloisForLFunctions.HTGeometry.GaussBonnetModelSurfaces
import GaloisForLFunctions.HTGeometry.GaussBonnetTorus
import GaloisForLFunctions.HTGeometry.GaussBonnetWarpedPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetPolarPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetTriangulatedTorus
import GaloisForLFunctions.HTGeometry.GaussBonnetGraph

/-!
# The Gauss--Bonnet theorem

This module is the capstone of the corpus' Gauss--Bonnet development.  It collects the
unconditional Lean statements proved in

* `GaussBonnetPlanarPartials` — planar partial derivatives and interval Fubini;
* `GaussBonnetOrthogonalPatch` — the local theorem on a coordinate rectangle;
* `GaussBonnetGeodesicPolar` — the local theorem for a geodesic disc on an arbitrary surface;
* `GaussBonnetPolarPatch`, `GaussBonnetWarpedPatch` — identification of the curvatures used there
  with the Gaussian curvature of the general orthogonal-coordinate formula;
* `GaussBonnetTorus` — the global theorem for doubly periodic metrics;
* `GaussBonnetWarped`, `GaussBonnetModelSurfaces` — the global theorem for surfaces of revolution,
  with the round sphere, the hyperbolic plane, the flat plane and the torus of revolution;
* `GaussBonnetPolyhedral`, `GaussBonnetPolyhedralModels`, `GaussBonnetTriangulatedTorus` — the
  global theorem for closed piecewise-flat surfaces of arbitrary genus, with the tetrahedron and
  the seven-vertex torus;
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
theorem gaussBonnet_geodesic_disc (C : GeodesicPolarChart) {R : ℝ} (hR : 0 < R) :
    C.totalCurvature R + C.boundaryTurning R = 2 * π :=
  C.gauss_bonnet_geodesic_disc hR

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

/-- **Gauss--Bonnet for finite simple graphs.**  The total combinatorial curvature is the Euler
characteristic. -/
theorem gaussBonnet_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ x : V, 2 * π * graphCurvature G x = 2 * π * graphEulerChar G :=
  gauss_bonnet_graph_two_pi G

end GaloisForLFunctions.HTGeometry.GaussBonnet
