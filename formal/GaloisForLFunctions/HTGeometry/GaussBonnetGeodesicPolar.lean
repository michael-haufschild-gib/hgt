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

/-- Where the chart is regular the curvature density is `-∂_r² f`. -/
theorem curvatureDensity_eq {r θ : ℝ} (hf : C.f (r, θ) ≠ 0) :
    C.gaussCurvature (r, θ) * C.areaDensity (r, θ) = -C.frr (r, θ) := by
  unfold gaussCurvature areaDensity
  field_simp

/-- The radial integral of the curvature density, for every fixed angle. -/
theorem radial_integral {R : ℝ} (hR : 0 < R) (θ : ℝ)
    (hne : ∀ r ∈ Set.Ioc (0 : ℝ) R, C.f (r, θ) ≠ 0) :
    (∫ r in (0 : ℝ)..R, C.gaussCurvature (r, θ) * C.areaDensity (r, θ)) = 1 - C.fr (R, θ) := by
  have hcongr : (∫ r in (0 : ℝ)..R, C.gaussCurvature (r, θ) * C.areaDensity (r, θ))
      = ∫ r in (0 : ℝ)..R, -C.frr (r, θ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Set.uIoc_of_le hR.le] at hr
    exact C.curvatureDensity_eq (hne r hr)
  rw [hcongr, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => C.hasDerivAt_fr r θ)
      ((continuous_sliceFst C.smooth_frr.continuous θ).intervalIntegrable 0 R)]
  have : C.fr (0, θ) = 1 := C.poleUnit θ
  rw [this]
  ring

/-- Away from the pole the boundary integrand is the radial derivative. -/
theorem boundary_integrand {R θ : ℝ} (hf : C.f (R, θ) ≠ 0) :
    C.circleGeodesicCurvature (R, θ) * C.areaDensity (R, θ) = C.fr (R, θ) := by
  unfold circleGeodesicCurvature areaDensity
  field_simp

/-- **Gauss--Bonnet for a geodesic disc.**  On an arbitrary smooth Riemannian surface,

```text
∫∫_{D_R} K dA + ∮_{∂D_R} κ_g ds = 2π = 2π · χ(disc).
```
-/
theorem gauss_bonnet_geodesic_disc {R : ℝ} (hR : 0 < R)
    (hne : ∀ θ : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) R, C.f (r, θ) ≠ 0) :
    C.totalCurvature R + C.boundaryTurning R = 2 * π := by
  have h1 : C.totalCurvature R = ∫ θ in (0 : ℝ)..(2 * π), (1 - C.fr (R, θ)) :=
    intervalIntegral.integral_congr fun θ _ => C.radial_integral hR θ (hne θ)
  have h2 : C.boundaryTurning R = ∫ θ in (0 : ℝ)..(2 * π), C.fr (R, θ) :=
    intervalIntegral.integral_congr fun θ _ =>
      C.boundary_integrand (hne θ R ⟨hR, le_refl R⟩)
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
  polePoint := fun _ => rfl
  poleUnit := flatPolarF_px

theorem flatPolarChart_f (r θ : ℝ) : flatPolarChart.f (r, θ) = r := rfl

/-! ### The round unit sphere, in geodesic polar coordinates -/

/-- The warping function of the unit sphere: `f(r, θ) = sin r`. -/
noncomputable def spherePolarF : ℝ × ℝ → ℝ := fun p => Real.sin p.1

theorem spherePolarF_px (θ : ℝ) : px spherePolarF (0, θ) = 1 := by
  have h : HasDerivAt (fun t : ℝ => spherePolarF (t, θ)) (px spherePolarF (0, θ)) 0 :=
    hasDerivAt_px (F := spherePolarF) (Real.contDiff_sin.comp contDiff_fst) 0 θ
  have h2 : HasDerivAt (fun t : ℝ => Real.sin t) (Real.cos 0) 0 := Real.hasDerivAt_sin 0
  simpa using h.unique h2

/-- The round unit sphere in geodesic polar coordinates around a pole: `dr² + sin(r)² dθ²`.
The chart is regular for `0 < r < π`. -/
noncomputable def spherePolarChart : GeodesicPolarChart where
  f := spherePolarF
  smooth := Real.contDiff_sin.comp contDiff_fst
  polePoint := fun _ => Real.sin_zero
  poleUnit := spherePolarF_px

theorem spherePolarChart_f (r θ : ℝ) : spherePolarChart.f (r, θ) = Real.sin r := rfl

/-- The spherical chart is regular strictly inside the injectivity radius. -/
theorem spherePolarChart_ne {r : ℝ} (h0 : 0 < r) (hpi : r < π) (θ : ℝ) :
    spherePolarChart.f (r, θ) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

/-! ### The hyperbolic plane, in geodesic polar coordinates -/

/-- The warping function of the hyperbolic plane: `f(r, θ) = sinh r`. -/
noncomputable def hyperbolicPolarF : ℝ × ℝ → ℝ := fun p => Real.sinh p.1

theorem hyperbolicPolarF_px (θ : ℝ) : px hyperbolicPolarF (0, θ) = 1 := by
  have h : HasDerivAt (fun t : ℝ => hyperbolicPolarF (t, θ)) (px hyperbolicPolarF (0, θ)) 0 :=
    hasDerivAt_px (F := hyperbolicPolarF) (Real.contDiff_sinh.comp contDiff_fst) 0 θ
  have h2 : HasDerivAt (fun t : ℝ => Real.sinh t) (Real.cosh 0) 0 := Real.hasDerivAt_sinh 0
  simpa using h.unique h2

/-- The hyperbolic plane in geodesic polar coordinates: `dr² + sinh(r)² dθ²`. -/
noncomputable def hyperbolicPolarChart : GeodesicPolarChart where
  f := hyperbolicPolarF
  smooth := Real.contDiff_sinh.comp contDiff_fst
  polePoint := fun _ => Real.sinh_zero
  poleUnit := hyperbolicPolarF_px

theorem hyperbolicPolarChart_f (r θ : ℝ) : hyperbolicPolarChart.f (r, θ) = Real.sinh r := rfl

/-- The hyperbolic chart is regular at every positive radius. -/
theorem hyperbolicPolarChart_ne {r : ℝ} (h0 : 0 < r) (θ : ℝ) :
    hyperbolicPolarChart.f (r, θ) ≠ 0 := by
  have : r ≠ 0 := h0.ne'
  simpa [hyperbolicPolarChart_f, Real.sinh_eq_zero] using this

/-! ### Curvature and Gauss--Bonnet on the model charts -/

theorem spherePolarChart_fr : spherePolarChart.fr = fun p : ℝ × ℝ => Real.cos p.1 := by
  funext p
  obtain ⟨r, θ⟩ := p
  have h : HasDerivAt (fun t : ℝ => spherePolarChart.f (t, θ)) (spherePolarChart.fr (r, θ)) r :=
    hasDerivAt_px spherePolarChart.smooth r θ
  exact h.unique (Real.hasDerivAt_sin r)

theorem spherePolarChart_frr : spherePolarChart.frr = fun p : ℝ × ℝ => -Real.sin p.1 := by
  funext p
  obtain ⟨r, θ⟩ := p
  have h : HasDerivAt (fun t : ℝ => spherePolarChart.fr (t, θ))
      (spherePolarChart.frr (r, θ)) r :=
    hasDerivAt_px spherePolarChart.smooth_fr r θ
  rw [spherePolarChart_fr] at h
  exact h.unique (Real.hasDerivAt_cos r)

/-- **The round unit sphere has Gaussian curvature `1`.** -/
theorem spherePolarChart_gaussCurvature {r : ℝ} (h0 : 0 < r) (hpi : r < π) (θ : ℝ) :
    spherePolarChart.gaussCurvature (r, θ) = 1 := by
  have hs : Real.sin r ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  unfold GeodesicPolarChart.gaussCurvature
  rw [spherePolarChart_frr, spherePolarChart_f]
  field_simp

/-- **Gauss--Bonnet for a geodesic disc on the round unit sphere**, at any radius below the
injectivity radius `π`. -/
theorem spherePolarChart_gauss_bonnet {R : ℝ} (h0 : 0 < R) (hpi : R < π) :
    spherePolarChart.totalCurvature R + spherePolarChart.boundaryTurning R = 2 * π :=
  spherePolarChart.gauss_bonnet_geodesic_disc h0 fun θ _r hr =>
    spherePolarChart_ne hr.1 (lt_of_le_of_lt hr.2 hpi) θ

theorem hyperbolicPolarChart_fr : hyperbolicPolarChart.fr = fun p : ℝ × ℝ => Real.cosh p.1 := by
  funext p
  obtain ⟨r, θ⟩ := p
  have h : HasDerivAt (fun t : ℝ => hyperbolicPolarChart.f (t, θ))
      (hyperbolicPolarChart.fr (r, θ)) r :=
    hasDerivAt_px hyperbolicPolarChart.smooth r θ
  exact h.unique (Real.hasDerivAt_sinh r)

theorem hyperbolicPolarChart_frr :
    hyperbolicPolarChart.frr = fun p : ℝ × ℝ => Real.sinh p.1 := by
  funext p
  obtain ⟨r, θ⟩ := p
  have h : HasDerivAt (fun t : ℝ => hyperbolicPolarChart.fr (t, θ))
      (hyperbolicPolarChart.frr (r, θ)) r :=
    hasDerivAt_px hyperbolicPolarChart.smooth_fr r θ
  rw [hyperbolicPolarChart_fr] at h
  exact h.unique (Real.hasDerivAt_cosh r)

/-- **The hyperbolic plane has Gaussian curvature `-1`.** -/
theorem hyperbolicPolarChart_gaussCurvature {r : ℝ} (h0 : 0 < r) (θ : ℝ) :
    hyperbolicPolarChart.gaussCurvature (r, θ) = -1 := by
  have hs : Real.sinh r ≠ 0 := by
    have : r ≠ 0 := h0.ne'
    simpa [Real.sinh_eq_zero] using this
  unfold GeodesicPolarChart.gaussCurvature
  rw [hyperbolicPolarChart_frr, hyperbolicPolarChart_f]
  field_simp

/-- **Gauss--Bonnet for a hyperbolic geodesic disc**, at every radius. -/
theorem hyperbolicPolarChart_gauss_bonnet {R : ℝ} (h0 : 0 < R) :
    hyperbolicPolarChart.totalCurvature R + hyperbolicPolarChart.boundaryTurning R = 2 * π :=
  hyperbolicPolarChart.gauss_bonnet_geodesic_disc h0 fun θ _r hr =>
    hyperbolicPolarChart_ne hr.1 θ

end GaloisForLFunctions.HTGeometry.GaussBonnet
