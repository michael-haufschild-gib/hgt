import GaloisForLFunctions.HTGeometry.GaussBonnetPolarPatch

/-!
# Radial arcs in a geodesic polar chart

A **radial arc** is a smooth positive radial graph `r = R(θ)` in a geodesic polar chart
`dr² + f(r,θ)² dθ²`.  This module carries the analytic core shared by all the star-shaped
Gauss--Bonnet statements: Liouville's formula for the geodesic curvature of a radial graph, and the
resulting **arc identity**

```text
∫_a^b ∫_0^{R(θ)} K dA  +  ∫_a^b κ_g ds  =  (b - a) - ( φ(b) - φ(a) ),
```

where `φ(θ) = arctan(R'(θ)/f(R(θ),θ))` measures the tangent direction of the arc against the
outward radial direction.  Everything else — the closed star-shaped region, and the star-shaped
geodesic polygon with corners — is obtained from this one identity by summing over arcs and
telescoping.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A smooth positive radial graph `r = R(θ)` in a geodesic polar chart. -/
structure RadialArc (C : GeodesicPolarChart) where
  /-- The radial graph function. -/
  R : ℝ → ℝ
  /-- The radial graph is smooth. -/
  smooth : ContDiff ℝ ∞ R
  /-- The arc avoids the pole. -/
  pos : ∀ θ, 0 < R θ

namespace RadialArc

variable {C : GeodesicPolarChart} (A : RadialArc C)

/-- `R'`. -/
noncomputable def R1 : ℝ → ℝ := deriv A.R

/-- `R''`. -/
noncomputable def R2 : ℝ → ℝ := deriv (deriv A.R)

/-- The warping function along the arc, `F(θ) = f(R(θ), θ)`. -/
noncomputable def F (θ : ℝ) : ℝ := C.f (A.R θ, θ)

/-- The radial derivative of the warping function along the arc. -/
noncomputable def Fr (θ : ℝ) : ℝ := px C.f (A.R θ, θ)

/-- The angular derivative of the warping function along the arc. -/
noncomputable def Fth (θ : ℝ) : ℝ := py C.f (A.R θ, θ)

theorem F_pos (θ : ℝ) : 0 < A.F θ := C.pos (A.R θ) θ (A.pos θ)

theorem smooth_R1 : ContDiff ℝ ∞ A.R1 := (contDiff_infty_iff_deriv.mp A.smooth).2

theorem hasDerivAt_R (θ : ℝ) : HasDerivAt A.R (A.R1 θ) θ :=
  (A.smooth.differentiable (by simp) θ).hasDerivAt

theorem hasDerivAt_R1 (θ : ℝ) : HasDerivAt A.R1 (A.R2 θ) θ :=
  (A.smooth_R1.differentiable (by simp) θ).hasDerivAt

theorem continuous_R1 : Continuous A.R1 := A.smooth_R1.continuous

theorem continuous_R2 : Continuous A.R2 :=
  (contDiff_infty_iff_deriv.mp A.smooth_R1).2.continuous

theorem continuous_pair : Continuous fun θ : ℝ => (A.R θ, θ) :=
  (A.smooth.continuous).prodMk continuous_id

theorem continuous_F : Continuous A.F := C.smooth.continuous.comp A.continuous_pair

theorem continuous_Fr : Continuous A.Fr := (continuous_px C.smooth).comp A.continuous_pair

theorem continuous_Fth : Continuous A.Fth := (continuous_py C.smooth).comp A.continuous_pair

/-- **The chain rule along the arc.** -/
theorem hasDerivAt_F (θ : ℝ) : HasDerivAt A.F (A.R1 θ * A.Fr θ + A.Fth θ) θ := by
  show HasDerivAt (fun s : ℝ => C.f (A.R s, s))
    (A.R1 θ * px C.f (A.R θ, θ) + py C.f (A.R θ, θ)) θ
  simpa using hasDerivAt_comp_curve C.smooth (A.hasDerivAt_R θ) (hasDerivAt_id θ)

/-- The Riemannian speed of the arc, `ds/dθ = √(R'² + F²)`. -/
noncomputable def speed (θ : ℝ) : ℝ := Real.sqrt (A.R1 θ ^ 2 + A.F θ ^ 2)

theorem speed_pos (θ : ℝ) : 0 < A.speed θ := by
  have := A.F_pos θ
  exact Real.sqrt_pos.mpr (by positivity)

theorem speed_sq (θ : ℝ) : A.speed θ ^ 2 = A.R1 θ ^ 2 + A.F θ ^ 2 := by
  have := A.F_pos θ
  exact Real.sq_sqrt (by positivity)

/-- **Liouville's geodesic curvature** of the radial graph. -/
noncomputable def kappa (θ : ℝ) : ℝ :=
  (2 * A.Fr θ * A.R1 θ ^ 2 + A.R1 θ * A.Fth θ - A.F θ * A.R2 θ + A.F θ ^ 2 * A.Fr θ)
    / A.speed θ ^ 3

/-- The arclength density of the geodesic curvature, `κ_g ds/dθ`. -/
noncomputable def kappaDs (θ : ℝ) : ℝ :=
  (2 * A.Fr θ * A.R1 θ ^ 2 + A.R1 θ * A.Fth θ - A.F θ * A.R2 θ + A.F θ ^ 2 * A.Fr θ)
    / (A.R1 θ ^ 2 + A.F θ ^ 2)

theorem kappa_mul_speed (θ : ℝ) : A.kappa θ * A.speed θ = A.kappaDs θ := by
  have hs : A.speed θ ≠ 0 := (A.speed_pos θ).ne'
  have hsq := A.speed_sq θ
  unfold kappa kappaDs
  rw [← hsq]
  field_simp

/-- The turning of the tangent relative to the outward radial direction. -/
noncomputable def turn (θ : ℝ) : ℝ := Real.arctan (A.R1 θ / A.F θ)

/-- **Liouville's formula.**  Along a radial arc the arclength density of the geodesic curvature is
the radial derivative of the warping function plus the turning rate of the tangent. -/
theorem hasDerivAt_turn (θ : ℝ) : HasDerivAt A.turn (A.Fr θ - A.kappaDs θ) θ := by
  have hF : A.F θ ≠ 0 := (A.F_pos θ).ne'
  have hq : HasDerivAt (fun t : ℝ => A.R1 t / A.F t)
      ((A.R2 θ * A.F θ - A.R1 θ * (A.R1 θ * A.Fr θ + A.Fth θ)) / A.F θ ^ 2) θ :=
    (A.hasDerivAt_R1 θ).div (A.hasDerivAt_F θ) hF
  have harctan := hq.arctan
  have hval : 1 / (1 + (A.R1 θ / A.F θ) ^ 2)
      * ((A.R2 θ * A.F θ - A.R1 θ * (A.R1 θ * A.Fr θ + A.Fth θ)) / A.F θ ^ 2)
      = A.Fr θ - A.kappaDs θ := by
    unfold kappaDs
    have hden : A.R1 θ ^ 2 + A.F θ ^ 2 ≠ 0 := by
      have := A.F_pos θ; positivity
    field_simp
    ring
  rw [hval] at harctan
  exact harctan

theorem continuous_kappaDs : Continuous A.kappaDs := by
  have hden : ∀ θ : ℝ, A.R1 θ ^ 2 + A.F θ ^ 2 ≠ 0 := fun θ => by
    have := A.F_pos θ; positivity
  unfold kappaDs
  exact (((continuous_const.mul A.continuous_Fr).mul (A.continuous_R1.pow 2)).add
    (A.continuous_R1.mul A.continuous_Fth) |>.sub (A.continuous_F.mul A.continuous_R2)
    |>.add ((A.continuous_F.pow 2).mul A.continuous_Fr)).div
    ((A.continuous_R1.pow 2).add (A.continuous_F.pow 2)) hden

/-- `∫∫ K dA` over the sector under the arc, for angles between `a` and `b`. -/
noncomputable def totalCurvatureOn (a b : ℝ) : ℝ :=
  ∫ θ in a..b, ∫ r in (0 : ℝ)..(A.R θ), C.gaussCurvature (r, θ) * C.areaDensity (r, θ)

/-- `∫ κ_g ds` along the arc, for angles between `a` and `b`. -/
noncomputable def boundaryTurningOn (a b : ℝ) : ℝ := ∫ θ in a..b, A.kappaDs θ

theorem totalCurvatureOn_eq (a b : ℝ) :
    A.totalCurvatureOn a b = ∫ θ in a..b, (1 - A.Fr θ) :=
  intervalIntegral.integral_congr fun θ _ => C.radial_integral (A.pos θ) θ

theorem boundaryTurningOn_eq (a b : ℝ) :
    A.boundaryTurningOn a b = (∫ θ in a..b, A.Fr θ) - (A.turn b - A.turn a) := by
  have hI1 : IntervalIntegrable A.Fr volume a b := A.continuous_Fr.intervalIntegrable a b
  have hI3 : IntervalIntegrable A.kappaDs volume a b :=
    A.continuous_kappaDs.intervalIntegrable a b
  have hI2 : IntervalIntegrable (fun θ : ℝ => A.Fr θ - A.kappaDs θ) volume a b :=
    (A.continuous_Fr.sub A.continuous_kappaDs).intervalIntegrable a b
  have hturn : (∫ θ in a..b, (A.Fr θ - A.kappaDs θ)) = A.turn b - A.turn a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => A.hasDerivAt_turn θ) hI2
  have hsplit : (∫ θ in a..b, (A.Fr θ - A.kappaDs θ))
      = (∫ θ in a..b, A.Fr θ) - A.boundaryTurningOn a b :=
    intervalIntegral.integral_sub hI1 hI3
  rw [hturn] at hsplit
  linarith [hsplit]

/-- **The arc identity.**  The curvature of the sector under a radial arc, plus the geodesic
turning of the arc, is the angle swept minus the turning of the tangent against the radial
direction. -/
theorem arc_identity (a b : ℝ) :
    A.totalCurvatureOn a b + A.boundaryTurningOn a b = (b - a) - (A.turn b - A.turn a) := by
  have hI1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b :=
    continuous_const.intervalIntegrable a b
  have hI2 : IntervalIntegrable A.Fr volume a b := A.continuous_Fr.intervalIntegrable a b
  rw [A.totalCurvatureOn_eq a b, A.boundaryTurningOn_eq a b,
    intervalIntegral.integral_sub hI1 hI2]
  simp

/-- **The Liouville curvature of a radial arc is the intrinsic geodesic curvature.** -/
theorem kappa_eq_geodesicCurvature (hpos : ∀ p, 0 < C.f p) (θ : ℝ) :
    A.kappa θ
      = (polarPatch C.smooth hpos).geodesicCurvature (A.R θ, θ) (A.R1 θ) 1 (A.R2 θ) 0 := by
  rw [polarPatch.geodesicCurvature_radialGraph]
  rfl

end RadialArc

end GaloisForLFunctions.HTGeometry.GaussBonnet
