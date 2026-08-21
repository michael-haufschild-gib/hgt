# Gauss--Bonnet theorem

- **ID:** gauss-bonnet
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** classical differential geometry; absent from mathlib
- **Statement:** `∫∫ K dA + ∮ κ_g ds + Σ exterior angles = 2π·χ`, in the local smooth, global smooth,
  global piecewise-flat and graph-theoretic categories.

## Goal
Mathlib has no Gauss--Bonnet theorem of any kind, and no Riemannian curvature at all
(`Mathlib/Geometry/Manifold/Riemannian/` contains only `Basic.lean` and `PathELength.lean`); it also
has no Jordan curve theorem, no Green's theorem for general plane regions, no integration of forms
over manifolds and no triangulation theory.  This card builds the theorem from scratch inside
`HTGeometry`, unconditionally.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: 13 Lean modules, `lake build` green, `#print axioms` = `{propext,
      Classical.choice, Quot.sound}` on every capstone
- [ ] 3 → 4  publication-ready

## What is proved (all unconditional, all in `GaloisForLFunctions.HTGeometry.GaussBonnet`)

### Smooth, local
| theorem | module |
|---|---|
| `OrthogonalPatch.gauss_bonnet_rectangle` — `∫∫_R K dA + ∮ κ_g ds + 4·(π/2) = 2π` for every smooth orthogonal Riemannian metric `E du² + G dv²` on any coordinate rectangle | `GaussBonnetOrthogonalPatch` |
| `OrthogonalPatch.totalCurvature_add_boundaryTurning` — the Green identity `∫∫ K dA = -∮ κ_g ds` | `GaussBonnetOrthogonalPatch` |
| `GeodesicPolarChart.gauss_bonnet_geodesic_disc` — `∫∫_{D_R} K dA + ∮ κ_g ds = 2π` for a geodesic disc on an **arbitrary** smooth surface | `GaussBonnetGeodesicPolar` |

### Smooth, global
| theorem | module |
|---|---|
| `OrthogonalPatch.gauss_bonnet_torus` — `∫∫_{T²} K dA = 0 = 2π·χ(T²)` for every smooth doubly periodic orthogonal metric | `GaussBonnetTorus` |
| `WarpProfile.gauss_bonnet_sphere_type` — `∫∫ K dA = 4π = 2π·χ(S²)` for every closed surface of revolution of sphere type | `GaussBonnetWarped` |
| `WarpProfile.gauss_bonnet_torus_type`, `gauss_bonnet_annulus`, `gauss_bonnet_disc` | `GaussBonnetWarped` |
| `roundSphere_gaussCurvature = 1/R²`, `roundSphere_totalCurvature = 4π`, `hyperbolicPlane_gaussCurvature = -1`, `flatPlane_gaussCurvature = 0`, `torusOfRevolution_totalCurvature = 0` | `GaussBonnetModelSurfaces` |

### Definitional certificates (the curvature really is the Gaussian curvature)
| theorem | module |
|---|---|
| `WarpProfile.toPatch_gaussCurvature` — the rotationally symmetric `-f''/f` is the general orthogonal-coordinate curvature | `GaussBonnetWarpedPatch` |
| `polarPatch.gaussCurvature_eq` — the geodesic-polar `-∂_r²f/f` likewise, for `f` depending on both variables | `GaussBonnetPolarPatch` |
| `polarPatch.uCurveGeodesicCurvature_eq = 0` — meridians are geodesics | `GaussBonnetPolarPatch` |

### Global, piecewise flat, arbitrary genus
| theorem | module |
|---|---|
| `ClosedTriangulation.gauss_bonnet_polyhedral` — `Σ_v (2π - Σ angles at v) = 2π·χ` | `GaussBonnetPolyhedral` |
| `ClosedTriangulation.ofRealization` — Euclidean realizations always give the angle structure (non-vacuity) | `GaussBonnetPolyhedralModels` |
| `tetrahedron_totalDefect = 4π`, `tetrahedron_eulerChar = 2` | `GaussBonnetPolyhedralModels` |
| `triangulatedTorus_totalDefect = 0`, `triangulatedTorus_eulerChar = 0` (Möbius 7-vertex torus) | `GaussBonnetTriangulatedTorus` |

### Graphs
| theorem | module |
|---|---|
| `gauss_bonnet_graph` — `Σ_x K(x) = χ(G)` for every finite simple graph | `GaussBonnetGraph` |

### Reusable infrastructure built on the way
`GaussBonnetPlanarPartials`: `px`/`py` partial derivatives on `ℝ × ℝ`, their smoothness, the slice
derivative certificates, and interval Fubini for continuous planar fields.

Capstone: `GaussBonnetTheorem`.

## Open residue (what is *not* proved)
The fully general smooth global statement `∫∫_M K dA = 2π·χ(M)` for an arbitrary compact Riemannian
surface is **not** proved, and cannot be with the present ingredients.  It needs either
- integration of 2-forms over oriented manifolds plus Stokes (absent from mathlib), or
- existence of a geodesic triangulation (Radó's theorem, absent everywhere), plus local
  Gauss--Bonnet on a *geodesic triangle*, which needs Green's theorem on non-rectangular plane
  regions.

The concrete next increments, in order:
1. an intrinsic geodesic curvature (Christoffel symbols and the covariant derivative along a curve
   for an orthogonal patch), upgrading the Liouville formulas of `GaussBonnetOrthogonalPatch` from
   definitions to theorems;
2. Liouville's formula `κ_g ds = dφ + ∂_r f dθ` for a curve `r = R(θ)` in geodesic polar
   coordinates;
3. Gauss--Bonnet for an arbitrary star-shaped region about the pole, hence for geodesic polygons
   containing the pole;
4. a gluing law turning a face-wise local theorem into the global one.

## Log
- 2026-08-21 — created directly at 3-formalized; 13 modules landed, axiom-clean, wired into
  `GaloisForLFunctions.HTGeometry`.
