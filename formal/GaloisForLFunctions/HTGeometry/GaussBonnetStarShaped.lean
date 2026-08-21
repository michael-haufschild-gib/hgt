import GaloisForLFunctions.HTGeometry.GaussBonnetPolarPatch

/-!
# Gauss--Bonnet for a star-shaped region on an arbitrary smooth surface

Let `dr² + f(r,θ)² dθ²` be a geodesic polar chart on a smooth Riemannian surface, and let

```text
Γ : θ ↦ (R(θ), θ),   R > 0,   R closed of period 2π
```

be a closed curve which is star-shaped about the pole.  Write `F(θ) = f(R(θ), θ)` for the warping
function along the curve and `R₁ = R'`, `R₂ = R''`.

Liouville's formula for the geodesic curvature of `Γ` reads

```text
κ_g = ( 2 f_r R₁² + R₁ f_θ - F R₂ + F² f_r ) / (R₁² + F²)^{3/2},
      ds/dθ = √(R₁² + F²),
```

so that

```text
κ_g ds = f_r dθ + dφ,      φ = -arctan(R₁/F)
```

is the radial part plus the turning of the tangent relative to the outward radial direction.  Since
the region is star-shaped, the radial Gauss--Bonnet computation gives

```text
∫∫_D K dA = ∫_0^{2π} ( ∂_r f(0,θ) - f_r(R(θ),θ) ) dθ = 2π - ∫_0^{2π} f_r dθ,
```

while the turning term integrates to zero around a closed curve.  Hence

```text
∫∫_D K dA + ∮_{∂D} κ_g ds = 2π = 2π · χ(disc)
```

for **every** star-shaped region on **every** smooth surface.  This strictly contains the geodesic
disc case of `GaussBonnetGeodesicPolar`, whose boundary is a coordinate circle `R ≡ const`.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A closed curve which is star-shaped about the pole of a geodesic polar chart. -/
structure StarCurve (C : GeodesicPolarChart) where
  /-- The radial graph function `r = R(θ)`. -/
  R : ℝ → ℝ
  /-- The radial graph is smooth. -/
  smooth : ContDiff ℝ ∞ R
  /-- The curve avoids the pole. -/
  pos : ∀ θ, 0 < R θ
  /-- The curve closes up. -/
  closedR : R (2 * π) = R 0
  /-- The curve closes up to first order. -/
  closedR' : deriv R (2 * π) = deriv R 0
  /-- The chart is `2π`-periodic in the angle along the curve. -/
  closedF : C.f (R 0, 2 * π) = C.f (R 0, 0)

namespace StarCurve

variable {C : GeodesicPolarChart} (S : StarCurve C)

/-- `R'`. -/
noncomputable def R1 : ℝ → ℝ := deriv S.R

/-- `R''`. -/
noncomputable def R2 : ℝ → ℝ := deriv (deriv S.R)

/-- The warping function along the curve, `F(θ) = f(R(θ), θ)`. -/
noncomputable def F (θ : ℝ) : ℝ := C.f (S.R θ, θ)

/-- The radial derivative of the warping function along the curve. -/
noncomputable def Fr (θ : ℝ) : ℝ := px C.f (S.R θ, θ)

/-- The angular derivative of the warping function along the curve. -/
noncomputable def Fth (θ : ℝ) : ℝ := py C.f (S.R θ, θ)

theorem F_pos (θ : ℝ) : 0 < S.F θ := C.pos (S.R θ) θ (S.pos θ)

theorem smooth_R1 : ContDiff ℝ ∞ S.R1 := (contDiff_infty_iff_deriv.mp S.smooth).2

theorem hasDerivAt_R (θ : ℝ) : HasDerivAt S.R (S.R1 θ) θ :=
  (S.smooth.differentiable (by simp) θ).hasDerivAt

theorem hasDerivAt_R1 (θ : ℝ) : HasDerivAt S.R1 (S.R2 θ) θ :=
  (S.smooth_R1.differentiable (by simp) θ).hasDerivAt

theorem continuous_R1 : Continuous S.R1 := S.smooth_R1.continuous

theorem continuous_R2 : Continuous S.R2 :=
  (contDiff_infty_iff_deriv.mp S.smooth_R1).2.continuous

theorem continuous_F : Continuous S.F := by
  have : Continuous fun θ : ℝ => (S.R θ, θ) := by
    exact (S.smooth.continuous).prodMk continuous_id
  exact C.smooth.continuous.comp this

theorem continuous_Fr : Continuous S.Fr := by
  have : Continuous fun θ : ℝ => (S.R θ, θ) := (S.smooth.continuous).prodMk continuous_id
  exact (continuous_px C.smooth).comp this

theorem continuous_Fth : Continuous S.Fth := by
  have : Continuous fun θ : ℝ => (S.R θ, θ) := (S.smooth.continuous).prodMk continuous_id
  exact (continuous_py C.smooth).comp this

/-- **The chain rule along the curve.** -/
theorem hasDerivAt_F (θ : ℝ) : HasDerivAt S.F (S.R1 θ * S.Fr θ + S.Fth θ) θ := by
  show HasDerivAt (fun s : ℝ => C.f (S.R s, s))
    (S.R1 θ * px C.f (S.R θ, θ) + py C.f (S.R θ, θ)) θ
  simpa using hasDerivAt_comp_curve C.smooth (S.hasDerivAt_R θ) (hasDerivAt_id θ)

/-- The Riemannian speed of the curve, `ds/dθ = √(R'² + F²)`. -/
noncomputable def speed (θ : ℝ) : ℝ := Real.sqrt (S.R1 θ ^ 2 + S.F θ ^ 2)

theorem speed_pos (θ : ℝ) : 0 < S.speed θ := by
  have := S.F_pos θ
  exact Real.sqrt_pos.mpr (by positivity)

theorem speed_sq (θ : ℝ) : S.speed θ ^ 2 = S.R1 θ ^ 2 + S.F θ ^ 2 := by
  have := S.F_pos θ
  exact Real.sq_sqrt (by positivity)

/-- **Liouville's geodesic curvature** of the star curve. -/
noncomputable def kappa (θ : ℝ) : ℝ :=
  (2 * S.Fr θ * S.R1 θ ^ 2 + S.R1 θ * S.Fth θ - S.F θ * S.R2 θ + S.F θ ^ 2 * S.Fr θ)
    / S.speed θ ^ 3

/-- The arclength density of the geodesic curvature, `κ_g ds/dθ`. -/
noncomputable def kappaDs (θ : ℝ) : ℝ :=
  (2 * S.Fr θ * S.R1 θ ^ 2 + S.R1 θ * S.Fth θ - S.F θ * S.R2 θ + S.F θ ^ 2 * S.Fr θ)
    / (S.R1 θ ^ 2 + S.F θ ^ 2)

theorem kappa_mul_speed (θ : ℝ) : S.kappa θ * S.speed θ = S.kappaDs θ := by
  have hs : S.speed θ ≠ 0 := (S.speed_pos θ).ne'
  have hsq := S.speed_sq θ
  unfold kappa kappaDs
  rw [← hsq]
  field_simp

/-- The turning of the tangent relative to the outward radial direction. -/
noncomputable def turn (θ : ℝ) : ℝ := Real.arctan (S.R1 θ / S.F θ)

/-- **Liouville's formula.**  Along a star curve the arclength density of the geodesic curvature is
the radial derivative of the warping function plus the turning rate of the tangent. -/
theorem hasDerivAt_turn (θ : ℝ) : HasDerivAt S.turn (S.Fr θ - S.kappaDs θ) θ := by
  have hF : S.F θ ≠ 0 := (S.F_pos θ).ne'
  have hq : HasDerivAt (fun t : ℝ => S.R1 t / S.F t)
      ((S.R2 θ * S.F θ - S.R1 θ * (S.R1 θ * S.Fr θ + S.Fth θ)) / S.F θ ^ 2) θ :=
    (S.hasDerivAt_R1 θ).div (S.hasDerivAt_F θ) hF
  have harctan := hq.arctan
  have hval : 1 / (1 + (S.R1 θ / S.F θ) ^ 2)
      * ((S.R2 θ * S.F θ - S.R1 θ * (S.R1 θ * S.Fr θ + S.Fth θ)) / S.F θ ^ 2)
      = S.Fr θ - S.kappaDs θ := by
    unfold kappaDs
    have hden : S.R1 θ ^ 2 + S.F θ ^ 2 ≠ 0 := by
      have := S.F_pos θ; positivity
    field_simp
    ring
  rw [hval] at harctan
  exact harctan

theorem continuous_kappaDs : Continuous S.kappaDs := by
  have hden : ∀ θ : ℝ, S.R1 θ ^ 2 + S.F θ ^ 2 ≠ 0 := fun θ => by
    have := S.F_pos θ; positivity
  unfold kappaDs
  exact (((continuous_const.mul S.continuous_Fr).mul (S.continuous_R1.pow 2)).add
    (S.continuous_R1.mul S.continuous_Fth) |>.sub (S.continuous_F.mul S.continuous_R2)
    |>.add ((S.continuous_F.pow 2).mul S.continuous_Fr)).div
    ((S.continuous_R1.pow 2).add (S.continuous_F.pow 2)) hden

theorem turn_closed : S.turn (2 * π) = S.turn 0 := by
  have hR1 : S.R1 (2 * π) = S.R1 0 := S.closedR'
  have hF : S.F (2 * π) = S.F 0 := by
    unfold F
    rw [S.closedR, S.closedF]
  unfold turn
  rw [hR1, hF]

/-- The total curvature `∫∫_D K dA` of the star-shaped region. -/
noncomputable def totalCurvature : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), ∫ r in (0 : ℝ)..(S.R θ),
    C.gaussCurvature (r, θ) * C.areaDensity (r, θ)

/-- The total geodesic turning `∮_{∂D} κ_g ds` of the boundary curve. -/
noncomputable def boundaryTurning : ℝ := ∫ θ in (0 : ℝ)..(2 * π), S.kappaDs θ

theorem totalCurvature_eq : S.totalCurvature = ∫ θ in (0 : ℝ)..(2 * π), (1 - S.Fr θ) :=
  intervalIntegral.integral_congr fun θ _ => C.radial_integral (S.pos θ) θ

theorem boundaryTurning_eq : S.boundaryTurning = ∫ θ in (0 : ℝ)..(2 * π), S.Fr θ := by
  have hI1 : IntervalIntegrable S.Fr volume 0 (2 * π) :=
    S.continuous_Fr.intervalIntegrable 0 (2 * π)
  have hI2 : IntervalIntegrable (fun θ : ℝ => S.Fr θ - S.kappaDs θ) volume 0 (2 * π) :=
    (S.continuous_Fr.sub S.continuous_kappaDs).intervalIntegrable 0 (2 * π)
  have hturn : (∫ θ in (0 : ℝ)..(2 * π), (S.Fr θ - S.kappaDs θ)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => S.hasDerivAt_turn θ) hI2,
      S.turn_closed]
    ring
  have hsplit : (∫ θ in (0 : ℝ)..(2 * π), (S.Fr θ - S.kappaDs θ))
      = (∫ θ in (0 : ℝ)..(2 * π), S.Fr θ) - S.boundaryTurning :=
    intervalIntegral.integral_sub hI1 (S.continuous_kappaDs.intervalIntegrable 0 (2 * π))
  rw [hturn] at hsplit
  linarith [hsplit]

/-- **The Liouville curvature of a star curve is the intrinsic geodesic curvature.**  Whenever the
chart is regular everywhere, `kappa` agrees with the covariant-derivative definition of geodesic
curvature from `GaussBonnetGeodesicCurvature`. -/
theorem kappa_eq_geodesicCurvature (hpos : ∀ p, 0 < C.f p) (θ : ℝ) :
    S.kappa θ
      = (polarPatch C.smooth hpos).geodesicCurvature (S.R θ, θ) (S.R1 θ) 1 (S.R2 θ) 0 := by
  rw [polarPatch.geodesicCurvature_radialGraph]
  rfl

/-- **Gauss--Bonnet for a star-shaped region on an arbitrary smooth surface.**

```text
∫∫_D K dA + ∮_{∂D} κ_g ds = 2π = 2π·χ(disc).
```
-/
theorem gauss_bonnet_star : S.totalCurvature + S.boundaryTurning = 2 * π := by
  have hI1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (2 * π) :=
    continuous_const.intervalIntegrable 0 (2 * π)
  have hI2 : IntervalIntegrable S.Fr volume 0 (2 * π) :=
    S.continuous_Fr.intervalIntegrable 0 (2 * π)
  rw [S.totalCurvature_eq, S.boundaryTurning_eq, intervalIntegral.integral_sub hI1 hI2]
  simp

end StarCurve

end GaloisForLFunctions.HTGeometry.GaussBonnet
