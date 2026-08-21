import GaloisForLFunctions.HTGeometry.GaussBonnetOrthogonalPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetGeodesicPolar

/-!
# Geodesic polar coordinates as an orthogonal coordinate patch

The curvature used in `GaussBonnetGeodesicPolar` is `K = -∂_r² f / f`.  This module proves that it
really is the Gaussian curvature: for the metric `dr² + f(r,θ)² dθ²`, i.e. the orthogonal patch
`E = 1`, `G = f²`, the general orthogonal-coordinate curvature formula

```text
K = -1/(2√(EG)) ( ∂_θ(E_θ/√(EG)) + ∂_r(G_r/√(EG)) )
```

evaluates to `-∂_r² f / f`, the area density `√(EG)` evaluates to `f`, the meridians `θ = const`
have geodesic curvature `0` (they are geodesics — this is what "geodesic polar coordinates" means),
and the circles `r = const` have geodesic curvature `∂_r f / f`.

Unlike `GaussBonnetWarpedPatch`, the warping function here is allowed to depend on both
coordinates, so this covers an arbitrary smooth surface, not only the rotationally symmetric ones.
-/

open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

variable {f : ℝ × ℝ → ℝ}

/-- The metric `dr² + f(r,θ)² dθ²` as an orthogonal coordinate patch. -/
noncomputable def polarPatch (hf : ContDiff ℝ ∞ f) (hpos : ∀ p, 0 < f p) : OrthogonalPatch where
  E := fun _ => 1
  G := fun p => f p ^ 2
  smoothE := contDiff_const
  smoothG := hf.pow 2
  posE := fun _ => one_pos
  posG := fun p => pow_pos (hpos p) 2

namespace polarPatch

variable (hf : ContDiff ℝ ∞ f) (hpos : ∀ p, 0 < f p)

@[simp] theorem E_eq (p : ℝ × ℝ) : (polarPatch hf hpos).E p = 1 := rfl

@[simp] theorem G_eq (p : ℝ × ℝ) : (polarPatch hf hpos).G p = f p ^ 2 := rfl

theorem uSpeed_eq (p : ℝ × ℝ) : (polarPatch hf hpos).uSpeed p = 1 := by
  simp [OrthogonalPatch.uSpeed]

theorem vSpeed_eq (p : ℝ × ℝ) : (polarPatch hf hpos).vSpeed p = f p := by
  simp [OrthogonalPatch.vSpeed, Real.sqrt_sq (hpos p).le]

/-- The area density of `dr² + f² dθ²` is `f`. -/
theorem area_eq (p : ℝ × ℝ) : (polarPatch hf hpos).area p = f p := by
  simp [OrthogonalPatch.area, uSpeed_eq hf hpos, vSpeed_eq hf hpos]

theorem py_E (p : ℝ × ℝ) : py (polarPatch hf hpos).E p = 0 := by
  simp [py, show (polarPatch hf hpos).E = fun _ : ℝ × ℝ => (1 : ℝ) from rfl]

theorem Q_eq (p : ℝ × ℝ) : (polarPatch hf hpos).Q p = 0 := by
  simp [OrthogonalPatch.Q, py_E hf hpos]

theorem py_Q (p : ℝ × ℝ) : py (polarPatch hf hpos).Q p = 0 := by
  have h : (polarPatch hf hpos).Q = fun _ : ℝ × ℝ => (0 : ℝ) := funext fun p => Q_eq hf hpos p
  simp [py, h]

theorem px_G (r θ : ℝ) : px (polarPatch hf hpos).G (r, θ) = 2 * f (r, θ) * px f (r, θ) := by
  have h1 : HasDerivAt (fun t : ℝ => (polarPatch hf hpos).G (t, θ))
      (px (polarPatch hf hpos).G (r, θ)) r :=
    hasDerivAt_px (polarPatch hf hpos).smoothG r θ
  have h2 : HasDerivAt (fun t : ℝ => f (t, θ) ^ 2) (2 * f (r, θ) * px f (r, θ)) r := by
    refine ((hasDerivAt_px hf r θ).pow 2).congr_deriv ?_
    push_cast
    ring
  exact h1.unique h2

/-- The `dθ` component of the Liouville one-form is `∂_r f`. -/
theorem P_eq (r θ : ℝ) : (polarPatch hf hpos).P (r, θ) = px f (r, θ) := by
  have hne : f (r, θ) ≠ 0 := (hpos (r, θ)).ne'
  unfold OrthogonalPatch.P
  rw [px_G hf hpos r θ, area_eq hf hpos]
  field_simp

theorem px_P (r θ : ℝ) : px (polarPatch hf hpos).P (r, θ) = px (px f) (r, θ) := by
  have h1 : HasDerivAt (fun t : ℝ => (polarPatch hf hpos).P (t, θ))
      (px (polarPatch hf hpos).P (r, θ)) r :=
    hasDerivAt_px (polarPatch hf hpos).smooth_P r θ
  have heq : (fun t : ℝ => (polarPatch hf hpos).P (t, θ)) = fun t : ℝ => px f (t, θ) :=
    funext fun t => P_eq hf hpos t θ
  rw [heq] at h1
  exact h1.unique (hasDerivAt_px (contDiff_px hf) r θ)

/-- **The Gaussian curvature in geodesic polar coordinates is `-∂_r² f / f`.**  This identifies the
curvature used in `GaussBonnetGeodesicPolar` with the Gaussian curvature computed from the general
orthogonal-coordinate formula. -/
theorem gaussCurvature_eq (r θ : ℝ) :
    (polarPatch hf hpos).gaussCurvature (r, θ) = -px (px f) (r, θ) / f (r, θ) := by
  unfold OrthogonalPatch.gaussCurvature
  rw [px_P hf hpos r θ, py_Q hf hpos, area_eq hf hpos]
  ring_nf

/-- **Meridians are geodesics.** -/
theorem uCurveGeodesicCurvature_eq (p : ℝ × ℝ) :
    (polarPatch hf hpos).uCurveGeodesicCurvature p = 0 := by
  simp [OrthogonalPatch.uCurveGeodesicCurvature, py_E hf hpos]

/-- **The geodesic curvature of a geodesic circle is `∂_r f / f`.** -/
theorem vCurveGeodesicCurvature_eq (r θ : ℝ) :
    (polarPatch hf hpos).vCurveGeodesicCurvature (r, θ) = px f (r, θ) / f (r, θ) := by
  have hne : f (r, θ) ≠ 0 := (hpos (r, θ)).ne'
  unfold OrthogonalPatch.vCurveGeodesicCurvature
  rw [px_G hf hpos r θ, uSpeed_eq hf hpos, G_eq]
  field_simp

end polarPatch

/-- A geodesic polar chart which is regular everywhere is an orthogonal coordinate patch whose
Gaussian curvature is the one used in `GaussBonnetGeodesicPolar`. -/
theorem GeodesicPolarChart.gaussCurvature_eq_patch (C : GeodesicPolarChart)
    (hpos : ∀ p, 0 < C.f p) (r θ : ℝ) :
    (polarPatch C.smooth hpos).gaussCurvature (r, θ) = C.gaussCurvature (r, θ) :=
  polarPatch.gaussCurvature_eq C.smooth hpos r θ

/-- A geodesic polar chart which is regular everywhere has the geodesic curvature used in
`GaussBonnetGeodesicPolar` along its circles. -/
theorem GeodesicPolarChart.circleGeodesicCurvature_eq_patch (C : GeodesicPolarChart)
    (hpos : ∀ p, 0 < C.f p) (r θ : ℝ) :
    (polarPatch C.smooth hpos).vCurveGeodesicCurvature (r, θ)
      = C.circleGeodesicCurvature (r, θ) :=
  polarPatch.vCurveGeodesicCurvature_eq C.smooth hpos r θ

end GaloisForLFunctions.HTGeometry.GaussBonnet
