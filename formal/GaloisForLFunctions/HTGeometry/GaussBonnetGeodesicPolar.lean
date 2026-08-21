import GaloisForLFunctions.HTGeometry.GaussBonnetPlanarPartials

/-!
# Gauss--Bonnet for a geodesic disc on an arbitrary smooth surface

Around any point of any smooth Riemannian surface one may introduce **geodesic polar coordinates**
`(r, θ)`, in which the metric takes the form

```text
g = dr² + f(r, θ)² dθ²,     f(0, θ) = 0,   ∂_r f(0, θ) = 1.
```

Here `f` is an arbitrary smooth positive function of *both* variables: no rotational symmetry, no
curvature condition.  In these coordinates

```text
K = -∂_r² f / f,      dA = f dr dθ,      κ_g(r = const) = ∂_r f / f,   ds = f dθ,
```

so the whole Gauss--Bonnet theorem for a geodesic disc is the fundamental theorem of calculus in
the radial variable, applied for every fixed `θ`:

```text
∫∫_{D_R} K dA + ∮_{∂D_R} κ_g ds
  = ∫_0^{2π} ( ∂_r f(0,θ) - ∂_r f(R,θ) ) dθ + ∫_0^{2π} ∂_r f(R,θ) dθ
  = ∫_0^{2π} 1 dθ = 2π = 2π · χ(disc).
```

This is the local Gauss--Bonnet theorem in its classical geodesic-disc form, for an arbitrary
smooth surface.  The Gauss--Bonnet defect of the disc is carried entirely by the pole normalization
`∂_r f(0, θ) = 1`, which is exactly the condition that the metric closes up smoothly at the centre.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- **Geodesic polar coordinates** on a smooth Riemannian surface: the metric
`dr² + f(r,θ)² dθ²` with a smooth warping function that vanishes to first order at the pole. -/
structure GeodesicPolarChart where
  /-- The warping function `f(r, θ)`. -/
  f : ℝ × ℝ → ℝ
  /-- The warping function is smooth. -/
  smooth : ContDiff ℝ ∞ f
  /-- The coordinates are regular away from the pole. -/
  pos : ∀ r θ : ℝ, 0 < r → 0 < f (r, θ)
  /-- The pole is a point: the circles of radius `0` are degenerate. -/
  polePoint : ∀ θ : ℝ, f (0, θ) = 0
  /-- The metric closes up smoothly at the pole: the radial derivative there is `1`. -/
  poleUnit : ∀ θ : ℝ, px f (0, θ) = 1

namespace GeodesicPolarChart

variable (C : GeodesicPolarChart)

/-- The radial derivative `∂_r f`. -/
noncomputable def fr : ℝ × ℝ → ℝ := px C.f

/-- The second radial derivative `∂_r² f`. -/
noncomputable def frr : ℝ × ℝ → ℝ := px (px C.f)

theorem smooth_fr : ContDiff ℝ ∞ C.fr := contDiff_px C.smooth

theorem smooth_frr : ContDiff ℝ ∞ C.frr := contDiff_px C.smooth_fr

theorem hasDerivAt_fr (r θ : ℝ) : HasDerivAt (fun t : ℝ => C.fr (t, θ)) (C.frr (r, θ)) r :=
  hasDerivAt_px C.smooth_fr r θ

/-- **The Gaussian curvature in geodesic polar coordinates**, `K = -∂_r² f / f`. -/
noncomputable def gaussCurvature (p : ℝ × ℝ) : ℝ := -C.frr p / C.f p

/-- The area density: `dA = f dr dθ`. -/
noncomputable def areaDensity (p : ℝ × ℝ) : ℝ := C.f p

/-- **The geodesic curvature of the geodesic circle `r = const`**, `κ_g = ∂_r f / f`. -/
noncomputable def circleGeodesicCurvature (p : ℝ × ℝ) : ℝ := C.fr p / C.f p

/-- The total curvature `∫∫_{D_R} K dA` of the geodesic disc of radius `R`. -/
noncomputable def totalCurvature (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), ∫ r in (0 : ℝ)..R, C.gaussCurvature (r, θ) * C.areaDensity (r, θ)

/-- The total geodesic turning `∮_{∂D_R} κ_g ds` of the geodesic circle of radius `R`. -/
noncomputable def boundaryTurning (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), C.circleGeodesicCurvature (R, θ) * C.areaDensity (R, θ)

/-- Away from the pole the curvature density is `-∂_r² f`. -/
theorem curvatureDensity_eq {r θ : ℝ} (hr : 0 < r) :
    C.gaussCurvature (r, θ) * C.areaDensity (r, θ) = -C.frr (r, θ) := by
  have hf : C.f (r, θ) ≠ 0 := (C.pos r θ hr).ne'
  unfold gaussCurvature areaDensity
  field_simp

/-- The radial integral of the curvature density, for every fixed angle. -/
theorem radial_integral {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    (∫ r in (0 : ℝ)..R, C.gaussCurvature (r, θ) * C.areaDensity (r, θ)) = 1 - C.fr (R, θ) := by
  have hcongr : (∫ r in (0 : ℝ)..R, C.gaussCurvature (r, θ) * C.areaDensity (r, θ))
      = ∫ r in (0 : ℝ)..R, -C.frr (r, θ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Set.uIoc_of_le hR.le] at hr
    exact C.curvatureDensity_eq hr.1
  rw [hcongr, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => C.hasDerivAt_fr r θ)
      ((continuous_sliceFst C.smooth_frr.continuous θ).intervalIntegrable 0 R)]
  have : C.fr (0, θ) = 1 := C.poleUnit θ
  rw [this]
  ring

/-- Away from the pole the boundary integrand is the radial derivative. -/
theorem boundary_integrand {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    C.circleGeodesicCurvature (R, θ) * C.areaDensity (R, θ) = C.fr (R, θ) := by
  have hf : C.f (R, θ) ≠ 0 := (C.pos R θ hR).ne'
  unfold circleGeodesicCurvature areaDensity
  field_simp

/-- **Gauss--Bonnet for a geodesic disc.**  On an arbitrary smooth Riemannian surface,

```text
∫∫_{D_R} K dA + ∮_{∂D_R} κ_g ds = 2π = 2π · χ(disc).
```
-/
theorem gauss_bonnet_geodesic_disc {R : ℝ} (hR : 0 < R) :
    C.totalCurvature R + C.boundaryTurning R = 2 * π := by
  have h1 : C.totalCurvature R = ∫ θ in (0 : ℝ)..(2 * π), (1 - C.fr (R, θ)) :=
    intervalIntegral.integral_congr fun θ _ => C.radial_integral hR θ
  have h2 : C.boundaryTurning R = ∫ θ in (0 : ℝ)..(2 * π), C.fr (R, θ) :=
    intervalIntegral.integral_congr fun θ _ => C.boundary_integrand hR θ
  have hI1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (2 * π) :=
    continuous_const.intervalIntegrable 0 (2 * π)
  have hI2 : IntervalIntegrable (fun θ : ℝ => C.fr (R, θ)) volume 0 (2 * π) :=
    (continuous_sliceSnd C.smooth_fr.continuous R).intervalIntegrable 0 (2 * π)
  rw [h1, h2, intervalIntegral.integral_sub hI1 hI2]
  simp

end GeodesicPolarChart

/-! ### The flat plane, in geodesic polar coordinates -/

/-- The radial coordinate as a planar field. -/
def flatPolarF : ℝ × ℝ → ℝ := fun p => p.1

theorem flatPolarF_px (θ : ℝ) : px flatPolarF (0, θ) = 1 :=
  (hasDerivAt_px (F := flatPolarF) contDiff_fst 0 θ).unique (hasDerivAt_id 0)

/-- The Euclidean plane in geodesic polar coordinates: `f(r, θ) = r`. -/
def flatPolarChart : GeodesicPolarChart where
  f := flatPolarF
  smooth := contDiff_fst
  pos := fun _ _ h => h
  polePoint := fun _ => rfl
  poleUnit := flatPolarF_px

end GaloisForLFunctions.HTGeometry.GaussBonnet
