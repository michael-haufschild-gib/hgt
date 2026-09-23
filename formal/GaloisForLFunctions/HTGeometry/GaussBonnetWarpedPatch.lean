import GaloisForLFunctions.HTGeometry.GaussBonnetOrthogonalPatch
import GaloisForLFunctions.HTGeometry.GaussBonnetWarped

/-!
# The rotationally symmetric metric as an orthogonal coordinate patch

This module closes the loop between the two Gauss--Bonnet developments in the corpus.  A positive
warping profile `f` defines the orthogonal coordinate patch `E = 1`, `G = f(u)²`, i.e. the metric
`dr² + f(r)² dθ²`, and the general orthogonal-patch definitions specialize to the ones used for
rotationally symmetric surfaces:

* the general Gaussian curvature `K = -1/(2√(EG))(∂_v(E_v/√(EG)) + ∂_u(G_u/√(EG)))` becomes
  `-f''/f`;
* the area density `√(EG)` becomes `f`;
* the geodesic curvature of a meridian `θ = const` is `0` — meridians are geodesics;
* the geodesic curvature of a parallel `r = const` is `f'/f`.

So the curvature used in `GaussBonnetWarped` really is the Gaussian curvature of the metric, and
the geodesic curvature used there really is Liouville's.
-/

open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

namespace WarpProfile

variable (W : WarpProfile) (hpos : ∀ r, 0 < W.f r)

/-- A positive warping profile as an orthogonal coordinate patch: `E = 1`, `G = f(u)²`. -/
noncomputable def toPatch : OrthogonalPatch where
  E := fun _ => 1
  G := fun p => W.f p.1 ^ (2 : ℕ)
  smoothE := contDiff_const
  smoothG := (W.smooth.comp contDiff_fst).pow 2
  posE := fun _ => one_pos
  posG := fun p => pow_pos (hpos p.1) 2

variable {W}

@[simp] theorem toPatch_E (p : ℝ × ℝ) : (W.toPatch hpos).E p = 1 := rfl

@[simp] theorem toPatch_G (p : ℝ × ℝ) : (W.toPatch hpos).G p = W.f p.1 ^ (2 : ℕ) := rfl

theorem toPatch_uSpeed (p : ℝ × ℝ) : (W.toPatch hpos).uSpeed p = 1 := by
  simp [OrthogonalPatch.uSpeed]

theorem toPatch_vSpeed (p : ℝ × ℝ) : (W.toPatch hpos).vSpeed p = W.f p.1 := by
  simp [OrthogonalPatch.vSpeed, Real.sqrt_sq (hpos p.1).le]

/-- The area density of the rotationally symmetric metric is `f`. -/
theorem toPatch_area (p : ℝ × ℝ) : (W.toPatch hpos).area p = W.f p.1 := by
  simp [OrthogonalPatch.area, toPatch_uSpeed hpos, toPatch_vSpeed hpos]

theorem toPatch_py_E (p : ℝ × ℝ) : py (W.toPatch hpos).E p = 0 := by
  simp [py, show (W.toPatch hpos).E = fun _ : ℝ × ℝ => (1 : ℝ) from rfl]

/-- The `du` component of the Liouville form vanishes: the metric coefficient `E` is constant. -/
theorem toPatch_Q (p : ℝ × ℝ) : (W.toPatch hpos).Q p = 0 := by
  simp [OrthogonalPatch.Q, toPatch_py_E hpos]

theorem toPatch_py_Q (p : ℝ × ℝ) : py (W.toPatch hpos).Q p = 0 := by
  have h : (W.toPatch hpos).Q = fun _ : ℝ × ℝ => (0 : ℝ) := funext fun p => toPatch_Q hpos p
  simp [py, h]

theorem toPatch_px_G (u v : ℝ) :
    px (W.toPatch hpos).G (u, v) = 2 * W.f u * W.d1 u := by
  have h1 : HasDerivAt (fun t : ℝ => (W.toPatch hpos).G (t, v)) (px (W.toPatch hpos).G (u, v)) u :=
    hasDerivAt_px (W.toPatch hpos).smoothG u v
  have h2 : HasDerivAt (fun t : ℝ => W.f t ^ (2 : ℕ)) (2 * W.f u * W.d1 u) u := by
    refine ((W.hasDerivAt_f u).pow 2).congr_deriv ?_
    push_cast
    ring
  exact h1.unique h2

/-- The `dv` component of the Liouville form is `f'`. -/
theorem toPatch_P (u v : ℝ) : (W.toPatch hpos).P (u, v) = W.d1 u := by
  have hf : W.f u ≠ 0 := (hpos u).ne'
  unfold OrthogonalPatch.P
  rw [toPatch_px_G hpos u v, toPatch_area hpos]
  field_simp

theorem toPatch_px_P (u v : ℝ) : px (W.toPatch hpos).P (u, v) = W.d2 u := by
  have h1 : HasDerivAt (fun t : ℝ => (W.toPatch hpos).P (t, v)) (px (W.toPatch hpos).P (u, v)) u :=
    hasDerivAt_px (W.toPatch hpos).smooth_P u v
  have heq : (fun t : ℝ => (W.toPatch hpos).P (t, v)) = W.d1 :=
    funext fun t => toPatch_P hpos t v
  rw [heq] at h1
  exact h1.unique (W.hasDerivAt_d1 u)

/-- **The rotationally symmetric curvature is the Gaussian curvature.**  The general
orthogonal-coordinate curvature of `dr² + f(r)² dθ²` is `-f''/f`. -/
theorem toPatch_gaussCurvature (u v : ℝ) :
    (W.toPatch hpos).gaussCurvature (u, v) = W.gaussCurvature u := by
  unfold OrthogonalPatch.gaussCurvature WarpProfile.gaussCurvature
  rw [toPatch_px_P hpos u v, toPatch_py_Q hpos, toPatch_area hpos]
  ring_nf

/-- **Meridians are geodesics.** -/
theorem toPatch_uCurveGeodesicCurvature (p : ℝ × ℝ) :
    (W.toPatch hpos).uCurveGeodesicCurvature p = 0 := by
  simp [OrthogonalPatch.uCurveGeodesicCurvature, toPatch_py_E hpos]

/-- **The geodesic curvature of a parallel is `f'/f`.** -/
theorem toPatch_vCurveGeodesicCurvature (u v : ℝ) :
    (W.toPatch hpos).vCurveGeodesicCurvature (u, v) = W.parallelGeodesicCurvature u := by
  have hf : W.f u ≠ 0 := (hpos u).ne'
  unfold OrthogonalPatch.vCurveGeodesicCurvature WarpProfile.parallelGeodesicCurvature
  rw [toPatch_px_G hpos u v, toPatch_uSpeed hpos, toPatch_G]
  field_simp

end WarpProfile

end GaloisForLFunctions.HTGeometry.GaussBonnet
