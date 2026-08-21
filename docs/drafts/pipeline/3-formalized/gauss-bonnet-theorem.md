# Gauss--Bonnet theorem

- **ID:** gauss-bonnet
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** classical differential geometry; absent from mathlib
- **Statement:** `∫∫ K dA + ∮ κ_g ds + Σ exterior angles = 2π·χ`, in the local smooth, global smooth,
  global piecewise-flat and graph-theoretic categories.

## Goal
Mathlib has no Gauss--Bonnet theorem of any kind and essentially no Riemannian curvature
(`Mathlib/Geometry/Manifold/Riemannian/` contains only `Basic.lean` and `PathELength.lean`); it also
has no Jordan curve theorem, no Green's theorem for general plane regions, no integration of forms
over manifolds and no triangulation theory.  This card builds the theorem from scratch inside
`HTGeometry`, unconditionally.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: 20 Lean modules, `lake build` green, `#print axioms` =
      `{propext, Classical.choice, Quot.sound}` on every capstone, no `sorry`
- [ ] 3 → 4  publication-ready

## Capstone: `GaloisForLFunctions.HTGeometry.GaussBonnetTheorem`

| theorem | content |
|---|---|
| `gaussBonnet_local_rectangle` | `∫∫_R K dA + ∮ κ_g ds + 4·(π/2) = 2π` on any coordinate rectangle of any smooth orthogonal Riemannian metric |
| `gaussBonnet_geodesic_disc` | `∫∫ K dA + ∮ κ_g ds = 2π` for a geodesic disc on an **arbitrary** smooth surface, inside the injectivity radius |
| `gaussBonnet_sphere_disc`, `gaussBonnet_hyperbolic_disc` | the same on the round unit sphere (`K ≡ 1`, radius `< π`) and the hyperbolic plane (`K ≡ -1`, every radius) |
| `gaussBonnet_star_shaped` | the same for an arbitrary closed star-shaped region |
| `gaussBonnet_polygon` | the same **with corners**: `∫∫ K dA + ∮ κ_g ds + Σ ε_i = 2π` |
| `gaussBonnet_torus` | `∫∫_{T²} K dA = 0 = 2π·χ(T²)` for every smooth doubly periodic orthogonal metric |
| `gaussBonnet_sphere_type` | `∫∫ K dA = 4π = 2π·χ(S²)` for every closed surface of revolution of sphere type |
| `gaussBonnet_global` | `Σ_f ∫∫_f K dA = 2π·χ` for a closed surface assembled from Gauss--Bonnet faces glued isometrically |
| `gaussBonnet_polyhedral` | `Σ_v (2π - Σ angles at v) = 2π·χ` for closed piecewise-flat surfaces of any genus |
| `gaussBonnet_graph` | `Σ_x K(x) = χ(G)` for every finite simple graph |
| `gaussCurvature_eq_sectional` | the `K` used above **is** the sectional curvature `R₁₂₁₂/(EG)` of the Levi-Civita connection |
| `liouville_uCurve`, `liouville_vCurve` | the `κ_g` used above **is** the intrinsic geodesic curvature `⟨D_t c', N⟩/|c'|²` |

## Module map

Infrastructure
- `GaussBonnetPlanarPartials` — `px`/`py`, slice derivatives, chain rule along a plane curve,
  interval Fubini for continuous planar fields.
- `GaussBonnetPartialCalculus` — sum/product/quotient/neg/sqrt rules for `px`, `py`.

Smooth local
- `GaussBonnetOrthogonalPatch` — the Green identity `∫∫ K dA = -∮ κ_g ds` on a coordinate
  rectangle, and `gauss_bonnet_rectangle`.
- `GaussBonnetGeodesicPolar` — geodesic polar charts (regularity is a hypothesis where it is
  needed, not a global structure field, so the round sphere is covered up to its injectivity
  radius); `gauss_bonnet_geodesic_disc`; the flat, spherical and hyperbolic charts with their
  curvatures `0`, `1`, `-1`.
- `GaussBonnetRadialArc` — Liouville's formula `κ_g ds = ∂_r f dθ + dφ` for a radial graph, and the
  arc identity.
- `GaussBonnetStarShaped` — closed star-shaped regions.
- `GaussBonnetPolygon` — star-shaped polygons with corners; the angle-excess form for geodesic
  polygons; the Euclidean unit disc instance.

Intrinsic certification
- `GaussBonnetGeodesicCurvature` — Christoffel symbols, covariant acceleration, the intrinsic
  geodesic curvature; Liouville's formulas become theorems.
- `GaussBonnetRiemann` — the Riemann component `R¹₂₁₂`; the Gaussian curvature becomes the
  sectional curvature.
- `GaussBonnetPolarPatch`, `GaussBonnetWarpedPatch` — geodesic polar and rotationally symmetric
  metrics as orthogonal patches; meridians are geodesics.

Smooth global
- `GaussBonnetTorus` — doubly periodic metrics.
- `GaussBonnetWarped`, `GaussBonnetModelSurfaces` — surfaces of revolution; the round sphere
  (`K = 1/R²`, total `4π`), the hyperbolic plane (`K = -1`), the flat plane, the torus of
  revolution.
- `GaussBonnetGlobalAssembly` — the assembly law, with `ofStarPolygons` discharging the local
  identity, and the seven-vertex flat torus as an instance.

Piecewise flat and combinatorial
- `GaussBonnetPolyhedral` — `Σ_v defect(v) = 2π·χ`, any genus.
- `GaussBonnetPolyhedralModels` — Euclidean realizations (non-vacuity), the tetrahedron
  (`χ = 2`, defect `4π`).
- `GaussBonnetTriangulatedTorus` — the Möbius seven-vertex torus (`χ = 0`, defect `0`).
- `GaussBonnetGraph` — Knill's theorem for finite simple graphs.

## Open residue
The fully general smooth global statement `∫∫_M K dA = 2π·χ(M)` for an arbitrary compact Riemannian
**manifold** is not proved as a statement about manifolds, and cannot be with the present
ingredients: it needs either integration of 2-forms over oriented manifolds with Stokes (absent from
mathlib) or the existence of a geodesic triangulation (Radó's theorem, absent everywhere).  What is
proved instead is the assembly form: given a decomposition into Gauss--Bonnet faces glued
isometrically, the global identity follows, and the local identity on each face is a theorem.

Next increments:
1. a manifold-level definition of the surface, its charts and the gluing, so that `gluing` and
   `vertexAngles` in `ClosedSurfaceAssembly` become theorems rather than recorded data;
2. existence of a star-shaped geodesic-polygon decomposition subordinate to an atlas;
3. integration of 2-forms and Stokes, which would replace the whole assembly route.

## Log
- 2026-08-21 — created directly at 3-formalized; 20 modules landed, axiom-clean, wired into
  `GaloisForLFunctions.HTGeometry`.  `GeodesicPolarChart` carries no global positivity field, so
  the local theorems apply to every smooth surface inside its injectivity radius; `StarCurve`
  extends `RadialArc`, so the arc identity is stated once.
