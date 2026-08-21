import GaloisForLFunctions.HTGeometry.GaussBonnetRadialArc

/-!
# Gauss--Bonnet for a star-shaped region on an arbitrary smooth surface

A **star curve** is a closed radial arc `Γ : θ ↦ (R(θ), θ)`, `0 ≤ θ ≤ 2π`, in a geodesic polar
chart `dr² + f(r,θ)² dθ²`: the boundary of a region star-shaped about the pole.  The arc identity
of `GaussBonnetRadialArc`,

```text
∫_a^b ∫_0^{R(θ)} K dA + ∫_a^b κ_g ds = (b - a) - ( φ(b) - φ(a) ),
```

applied on `[0, 2π]` gives Gauss--Bonnet at once, because the tangent-direction angle `φ` returns to
its starting value around a closed curve:

```text
∫∫_D K dA + ∮_{∂D} κ_g ds = 2π = 2π · χ(disc).
```

This strictly contains the geodesic disc case of `GaussBonnetGeodesicPolar`, whose boundary is a
coordinate circle `R ≡ const`, and is itself the corner-free case of the star-shaped polygon
theorem of `GaussBonnetPolygon`.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A closed curve which is star-shaped about the pole of a geodesic polar chart. -/
structure StarCurve (C : GeodesicPolarChart) extends RadialArc C where
  /-- The curve closes up. -/
  closedPoint : R (2 * π) = R 0
  /-- The curve closes up to first order. -/
  closedDeriv : deriv R (2 * π) = deriv R 0
  /-- The chart is `2π`-periodic in the angle at the closing point. -/
  closedChart : C.f (R 0, 2 * π) = C.f (R 0, 0)

namespace StarCurve

variable {C : GeodesicPolarChart} (S : StarCurve C)

/-- The tangent direction returns to its starting value around a closed star curve. -/
theorem turn_closed : S.toRadialArc.turn (2 * π) = S.toRadialArc.turn 0 := by
  have hR1 : S.toRadialArc.R1 (2 * π) = S.toRadialArc.R1 0 := S.closedDeriv
  have hF : S.toRadialArc.F (2 * π) = S.toRadialArc.F 0 := by
    show C.f (S.R (2 * π), 2 * π) = C.f (S.R 0, 0)
    rw [S.closedPoint, S.closedChart]
  unfold RadialArc.turn
  rw [hR1, hF]

/-- The total curvature `∫∫_D K dA` of the star-shaped region. -/
noncomputable def totalCurvature : ℝ := S.toRadialArc.totalCurvatureOn 0 (2 * π)

/-- The total geodesic turning `∮_{∂D} κ_g ds` of the boundary curve. -/
noncomputable def boundaryTurning : ℝ := S.toRadialArc.boundaryTurningOn 0 (2 * π)

/-- **Gauss--Bonnet for a star-shaped region on an arbitrary smooth surface.**

```text
∫∫_D K dA + ∮_{∂D} κ_g ds = 2π = 2π·χ(disc).
```
-/
theorem gauss_bonnet_star : S.totalCurvature + S.boundaryTurning = 2 * π := by
  unfold totalCurvature boundaryTurning
  rw [S.toRadialArc.arc_identity 0 (2 * π), S.turn_closed]
  ring

/-- **The Liouville curvature of a star curve is the intrinsic geodesic curvature.**  Whenever the
chart is regular everywhere, `kappa` agrees with the covariant-derivative definition of geodesic
curvature from `GaussBonnetGeodesicCurvature`. -/
theorem kappa_eq_geodesicCurvature (hpos : ∀ p, 0 < C.f p) (θ : ℝ) :
    S.toRadialArc.kappa θ
      = (polarPatch C.smooth hpos).geodesicCurvature (S.R θ, θ) (S.toRadialArc.R1 θ) 1
          (S.toRadialArc.R2 θ) 0 :=
  S.toRadialArc.kappa_eq_geodesicCurvature hpos θ

end StarCurve

end GaloisForLFunctions.HTGeometry.GaussBonnet
