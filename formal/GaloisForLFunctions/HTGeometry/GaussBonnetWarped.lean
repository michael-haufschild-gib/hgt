import Mathlib

/-!
# Gauss--Bonnet for rotationally symmetric (warped-product) surfaces

A rotationally symmetric surface is the metric

```text
g = dr² + f(r)² dθ²
```

on a cylinder of coordinates `(r, θ)`, where the *warping profile* `f` is a smooth function of the
radial coordinate alone.  Every surface of revolution, parametrized by arclength along its profile
curve, is of this form; so are the round sphere, the flat plane in polar coordinates, the hyperbolic
plane, all tori of revolution, catenoids and pseudospheres.

For such a metric the classical orthogonal-coordinate curvature formula

```text
K = -1/(2√(EG)) · ( ∂_θ(E_θ/√(EG)) + ∂_r(G_r/√(EG)) ),   E = 1, G = f²
```

collapses to `K = -f''/f`, the area element is `dA = f dr dθ`, and the geodesic curvature of the
parallel `r = const`, traversed in the direction of increasing `θ`, is `κ_g = f'/f`.

The entire Gauss--Bonnet theorem for this class is then the fundamental theorem of calculus applied
to the identity `K · f = -f''`:

```text
∫∫ K dA  =  2π (f'(a) - f'(b))
```

over the annulus `a ≤ r ≤ b`.  All the classical global statements follow by reading off the
boundary behaviour of `f`:

* an annulus contributes `∫∫ K dA + ∮ κ_g ds = 0 = 2π·χ(annulus)`;
* a geodesic disc (a smooth pole at `r = a`, i.e. `f(a) = 0`, `f'(a) = 1`) contributes
  `∫∫ K dA + ∮ κ_g ds = 2π = 2π·χ(disc)`;
* a closed sphere-type surface (smooth poles at both ends) has total curvature
  `4π = 2π·χ(S²)`;
* a torus of revolution (periodic profile) has total curvature `0 = 2π·χ(T²)`.

Everything in this file is unconditional: no axioms, no hypotheses beyond the definition of the
object.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- The **warping profile** of a rotationally symmetric surface: a smooth function of the radial
coordinate, giving the metric `dr² + f(r)² dθ²`. -/
structure WarpProfile where
  /-- The profile function: `f r` is the radius of the parallel circle at radial parameter `r`. -/
  f : ℝ → ℝ
  /-- The profile is smooth. -/
  smooth : ContDiff ℝ ∞ f

namespace WarpProfile

variable (W : WarpProfile)

/-- The radial derivative of the profile. -/
noncomputable def d1 : ℝ → ℝ := deriv W.f

/-- The second radial derivative of the profile. -/
noncomputable def d2 : ℝ → ℝ := deriv (deriv W.f)

theorem smooth_d1 : ContDiff ℝ ∞ W.d1 := (contDiff_infty_iff_deriv.mp W.smooth).2

theorem hasDerivAt_f (r : ℝ) : HasDerivAt W.f (W.d1 r) r :=
  (W.smooth.differentiable (by simp) r).hasDerivAt

theorem hasDerivAt_d1 (r : ℝ) : HasDerivAt W.d1 (W.d2 r) r :=
  (W.smooth_d1.differentiable (by simp) r).hasDerivAt

theorem continuous_d2 : Continuous W.d2 :=
  (contDiff_infty_iff_deriv.mp W.smooth_d1).2.continuous

theorem continuous_f : Continuous W.f := W.smooth.continuous

theorem continuous_d1 : Continuous W.d1 := W.smooth_d1.continuous

/-- The **Gaussian curvature** of the rotationally symmetric metric `dr² + f(r)² dθ²`,
namely `K = -f''/f`. -/
noncomputable def gaussCurvature (r : ℝ) : ℝ := -W.d2 r / W.f r

/-- The **area density** of the metric in the coordinates `(r, θ)`: `dA = f dr dθ`. -/
noncomputable def areaDensity (r : ℝ) : ℝ := W.f r

/-- The **curvature density** `K · f`, i.e. the integrand of `∫∫ K dA` in the coordinates
`(r, θ)`.  Away from the coordinate singularities `f = 0` it agrees with `gaussCurvature · f`,
but as written it is smooth everywhere. -/
noncomputable def curvatureDensity (r : ℝ) : ℝ := -W.d2 r

/-- The **geodesic curvature** of the parallel `r = const`, traversed with increasing `θ`. -/
noncomputable def parallelGeodesicCurvature (r : ℝ) : ℝ := W.d1 r / W.f r

/-- The length of the parallel `r = const`. -/
noncomputable def parallelLength (r : ℝ) : ℝ := 2 * π * W.f r

/-- The total geodesic turning `∮ κ_g ds` along the parallel `r = const`. -/
noncomputable def parallelTurning (r : ℝ) : ℝ := 2 * π * W.d1 r

/-- The total curvature `∫∫ K dA` of the annulus `a ≤ r ≤ b`, written as an iterated integral in
the coordinates `(r, θ)`. -/
noncomputable def totalCurvature (a b : ℝ) : ℝ :=
  ∫ _θ in (0 : ℝ)..(2 * π), ∫ r in a..b, W.gaussCurvature r * W.areaDensity r

variable {W}

/-- Off the coordinate singularity the curvature density is what it should be. -/
theorem curvatureDensity_eq_mul {r : ℝ} (hr : W.f r ≠ 0) :
    W.curvatureDensity r = W.gaussCurvature r * W.areaDensity r := by
  unfold curvatureDensity gaussCurvature areaDensity
  field_simp

/-- Off the coordinate singularity the geodesic turning is length times geodesic curvature. -/
theorem parallelTurning_eq_length_mul {r : ℝ} (hr : W.f r ≠ 0) :
    W.parallelTurning r = W.parallelLength r * W.parallelGeodesicCurvature r := by
  unfold parallelTurning parallelLength parallelGeodesicCurvature
  field_simp

variable (W)

/-- **The radial fundamental theorem.**  The radial integral of the curvature density is the drop
of the profile slope across the interval. -/
theorem integral_curvatureDensity (a b : ℝ) :
    (∫ r in a..b, W.curvatureDensity r) = W.d1 a - W.d1 b := by
  have h : (∫ r in a..b, -W.d2 r) = -(W.d1 b - W.d1 a) := by
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => W.hasDerivAt_d1 r)
        (W.continuous_d2.intervalIntegrable a b)]
  simpa [curvatureDensity] using h.trans (by ring)

variable {W}

/-- On an annulus free of coordinate singularities the curvature integrand agrees almost
everywhere with the smooth curvature density. -/
theorem integral_gaussCurvature_mul_areaDensity {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0) :
    (∫ r in a..b, W.gaussCurvature r * W.areaDensity r) = W.d1 a - W.d1 b := by
  rw [← integral_curvatureDensity W a b]
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ b := by
    have : (volume ({b} : Set ℝ)) = 0 := Real.volume_singleton
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr this] with r hr
    simpa using hr
  filter_upwards [hb] with r hrb hr
  rw [Set.uIoc_of_le hab] at hr
  exact (curvatureDensity_eq_mul (hne r ⟨hr.1, lt_of_le_of_ne hr.2 hrb⟩)).symm

/-- **Gauss--Bonnet for a rotationally symmetric annulus.**  The total curvature of the annulus
`a ≤ r ≤ b` equals `2π` times the drop of the profile slope. -/
theorem totalCurvature_eq {a b : ℝ} (hab : a ≤ b) (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0) :
    W.totalCurvature a b = 2 * π * (W.d1 a - W.d1 b) := by
  unfold totalCurvature
  rw [integral_gaussCurvature_mul_areaDensity hab hne]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- **Gauss--Bonnet for an annulus**, in the classical shape
`∫∫ K dA + ∮_{∂} κ_g ds = 2π·χ`, with `χ(annulus) = 0`.  The outer parallel is traversed
positively and the inner parallel negatively. -/
theorem gauss_bonnet_annulus {a b : ℝ} (hab : a ≤ b) (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0) :
    W.totalCurvature a b + (W.parallelTurning b - W.parallelTurning a) = 0 := by
  rw [totalCurvature_eq hab hne]
  unfold parallelTurning
  ring

/-- **Gauss--Bonnet for a geodesic disc.**  If the profile has a smooth pole at `r = a`
(`f a = 0` and `f' a = 1`, the exact smoothness condition for the metric to close up at the
axis), then

```text
∫∫ K dA + ∮ κ_g ds = 2π = 2π·χ(disc).
```
-/
theorem gauss_bonnet_disc {a b : ℝ} (hab : a ≤ b) (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0)
    (hpole : W.d1 a = 1) :
    W.totalCurvature a b + W.parallelTurning b = 2 * π := by
  rw [totalCurvature_eq hab hne]
  unfold parallelTurning
  rw [hpole]
  ring

/-- **Gauss--Bonnet for a closed rotationally symmetric surface of sphere type.**  If the profile
has smooth poles at both ends (`f' a = 1` and `f' b = -1`), the total curvature is `4π`, that is
`2π·χ(S²)`. -/
theorem gauss_bonnet_sphere_type {a b : ℝ} (hab : a ≤ b) (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0)
    (hpoleA : W.d1 a = 1) (hpoleB : W.d1 b = -1) :
    W.totalCurvature a b = 2 * π * 2 := by
  rw [totalCurvature_eq hab hne, hpoleA, hpoleB]
  ring

/-- **Gauss--Bonnet for a torus of revolution.**  A closed profile (equal slopes at the two ends of
one period) has total curvature `0 = 2π·χ(T²)`. -/
theorem gauss_bonnet_torus_type {a b : ℝ} (hab : a ≤ b) (hne : ∀ r ∈ Set.Ioo a b, W.f r ≠ 0)
    (hclosed : W.d1 a = W.d1 b) :
    W.totalCurvature a b = 2 * π * 0 := by
  rw [totalCurvature_eq hab hne, hclosed]
  ring

end WarpProfile

end GaloisForLFunctions.HTGeometry.GaussBonnet
