import GaloisForLFunctions.HTGeometry.GaussBonnetWarped

/-!
# Model rotationally symmetric surfaces and their Gauss--Bonnet totals

This module instantiates `GaussBonnet.WarpProfile` on the four classical model surfaces and
certifies, unconditionally, that the abstract curvature `K = -f''/f` of
`GaussBonnetWarped` really is the Gaussian curvature in each case, together with the
Gauss--Bonnet total predicted by the Euler characteristic:

| surface | profile `f` | curvature | Gauss--Bonnet total |
|---|---|---|---|
| flat plane (polar) | `r` | `0` | `∫∫ K dA + ∮ κ_g ds = 2π = 2π·χ(disc)` |
| round sphere of radius `R` | `R sin(r/R)` | `1/R²` | `∫∫ K dA = 4π = 2π·χ(S²)` |
| hyperbolic plane | `sinh r` | `-1` | `∫∫ K dA + ∮ κ_g ds = 2π = 2π·χ(disc)` |
| torus of revolution | `R + ρ cos(r/ρ)` | `cos(r/ρ)/(ρ(R + ρ cos(r/ρ)))` | `∫∫ K dA = 0 = 2π·χ(T²)` |

These are genuine consistency certificates: for the round sphere the curvature is the constant
`1/R²`, so the total curvature `4π` is exactly `(1/R²) · 4πR²`, the classical area of the sphere.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

namespace WarpProfile

/-- Reading off the first radial derivative from a pointwise derivative certificate. -/
theorem d1_eq {W : WarpProfile} {g : ℝ → ℝ} (h : ∀ r, HasDerivAt W.f (g r) r) : W.d1 = g :=
  funext fun r => (h r).deriv

/-- Reading off the second radial derivative from the first. -/
theorem d2_eq {W : WarpProfile} {g h : ℝ → ℝ} (h1 : W.d1 = g)
    (h2 : ∀ r, HasDerivAt g (h r) r) : W.d2 = h := by
  have : W.d2 = deriv W.d1 := rfl
  rw [this, h1]
  exact funext fun r => (h2 r).deriv

end WarpProfile

/-! ### The flat plane in geodesic polar coordinates -/

/-- The Euclidean plane in geodesic polar coordinates: `dr² + r² dθ²`. -/
def flatPlane : WarpProfile := ⟨id, contDiff_id⟩

@[simp] theorem flatPlane_f (r : ℝ) : flatPlane.f r = r := rfl

theorem flatPlane_d1 : flatPlane.d1 = fun _ => (1 : ℝ) :=
  WarpProfile.d1_eq fun r => hasDerivAt_id r

theorem flatPlane_d2 : flatPlane.d2 = fun _ => (0 : ℝ) :=
  WarpProfile.d2_eq flatPlane_d1 fun r => hasDerivAt_const r (1 : ℝ)

/-- The Euclidean plane is flat. -/
theorem flatPlane_gaussCurvature (r : ℝ) : flatPlane.gaussCurvature r = 0 := by
  simp [WarpProfile.gaussCurvature, flatPlane_d2]

/-- **Gauss--Bonnet for a Euclidean disc.**  Total curvature `0`, total turning `2π`. -/
theorem flatPlane_gauss_bonnet_disc {b : ℝ} (hb : 0 < b) :
    flatPlane.totalCurvature 0 b + flatPlane.parallelTurning b = 2 * π := by
  refine WarpProfile.gauss_bonnet_disc hb.le ?_ ?_
  · intro r hr
    simpa using ne_of_gt hr.1
  · simp [flatPlane_d1]

/-! ### The round sphere -/

/-- The round sphere of radius `R`, in geodesic polar coordinates around a pole:
`dr² + (R sin(r/R))² dθ²`. -/
noncomputable def roundSphere (R : ℝ) : WarpProfile :=
  ⟨fun r => R * Real.sin (r / R), by fun_prop⟩

@[simp] theorem roundSphere_f (R r : ℝ) : (roundSphere R).f r = R * Real.sin (r / R) := rfl

theorem roundSphere_d1 {R : ℝ} (hR : R ≠ 0) :
    (roundSphere R).d1 = fun r => Real.cos (r / R) := by
  refine WarpProfile.d1_eq fun r => ?_
  have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) r := (hasDerivAt_id r).div_const R
  have h2 : HasDerivAt (Real.sin ∘ fun x : ℝ => x / R) (Real.cos (r / R) * (1 / R)) r :=
    (Real.hasDerivAt_sin (r / R)).comp r h1
  rw [Function.comp_def] at h2
  have h3 := h2.const_mul R
  have : R * (Real.cos (r / R) * (1 / R)) = Real.cos (r / R) := by field_simp
  rw [this] at h3
  exact h3

theorem roundSphere_d2 {R : ℝ} (hR : R ≠ 0) :
    (roundSphere R).d2 = fun r => -(Real.sin (r / R) / R) := by
  refine WarpProfile.d2_eq (roundSphere_d1 hR) fun r => ?_
  have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) r := (hasDerivAt_id r).div_const R
  have h2 : HasDerivAt (Real.cos ∘ fun x : ℝ => x / R) (-Real.sin (r / R) * (1 / R)) r :=
    (Real.hasDerivAt_cos (r / R)).comp r h1
  rw [Function.comp_def] at h2
  have : -Real.sin (r / R) * (1 / R) = -(Real.sin (r / R) / R) := by ring
  rw [this] at h2
  exact h2

/-- **The round sphere of radius `R` has constant Gaussian curvature `1/R²`.** -/
theorem roundSphere_gaussCurvature {R r : ℝ} (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0) :
    (roundSphere R).gaussCurvature r = 1 / R ^ (2 : ℕ) := by
  unfold WarpProfile.gaussCurvature
  rw [roundSphere_d2 hR, roundSphere_f]
  field_simp

/-- **Gauss--Bonnet for the round sphere.**  The total curvature is `4π = 2π·χ(S²)`. -/
theorem roundSphere_totalCurvature {R : ℝ} (hR : 0 < R) :
    (roundSphere R).totalCurvature 0 (π * R) = 4 * π := by
  have hR' : R ≠ 0 := ne_of_gt hR
  have hpi := Real.pi_pos
  have hab : (0 : ℝ) ≤ π * R := by positivity
  have key := WarpProfile.gauss_bonnet_sphere_type (W := roundSphere R) hab ?_ ?_ ?_
  · rw [key]; ring
  · intro r hr
    have h0 : 0 < r / R := div_pos hr.1 hR
    have h1 : r / R < π := by
      rw [div_lt_iff₀ hR]
      simpa [mul_comm] using hr.2
    have := Real.sin_pos_of_pos_of_lt_pi h0 h1
    simp only [roundSphere_f]
    positivity
  · rw [roundSphere_d1 hR']; simp
  · rw [roundSphere_d1 hR']
    simp [mul_div_assoc, div_self hR']

/-! ### The hyperbolic plane -/

/-- The hyperbolic plane in geodesic polar coordinates: `dr² + sinh(r)² dθ²`. -/
noncomputable def hyperbolicPlane : WarpProfile := ⟨Real.sinh, Real.contDiff_sinh⟩

@[simp] theorem hyperbolicPlane_f (r : ℝ) : hyperbolicPlane.f r = Real.sinh r := rfl

theorem hyperbolicPlane_d1 : hyperbolicPlane.d1 = Real.cosh :=
  WarpProfile.d1_eq fun r => Real.hasDerivAt_sinh r

theorem hyperbolicPlane_d2 : hyperbolicPlane.d2 = Real.sinh :=
  WarpProfile.d2_eq hyperbolicPlane_d1 fun r => Real.hasDerivAt_cosh r

/-- **The hyperbolic plane has constant Gaussian curvature `-1`.** -/
theorem hyperbolicPlane_gaussCurvature {r : ℝ} (hr : r ≠ 0) :
    hyperbolicPlane.gaussCurvature r = -1 := by
  have hs : Real.sinh r ≠ 0 := by
    simpa [Real.sinh_eq_zero] using hr
  unfold WarpProfile.gaussCurvature
  rw [hyperbolicPlane_d2, hyperbolicPlane_f]
  field_simp

/-- **Gauss--Bonnet for a hyperbolic disc.** -/
theorem hyperbolicPlane_gauss_bonnet_disc {b : ℝ} (hb : 0 < b) :
    hyperbolicPlane.totalCurvature 0 b + hyperbolicPlane.parallelTurning b = 2 * π := by
  refine WarpProfile.gauss_bonnet_disc hb.le ?_ ?_
  · intro r hr
    have : r ≠ 0 := ne_of_gt hr.1
    simpa [Real.sinh_eq_zero] using this
  · simp [hyperbolicPlane_d1]

/-- The total curvature of a hyperbolic disc of radius `b` is minus its area
`2π(cosh b - 1)`. -/
theorem hyperbolicPlane_totalCurvature {b : ℝ} (hb : 0 < b) :
    hyperbolicPlane.totalCurvature 0 b = -(2 * π * (Real.cosh b - 1)) := by
  rw [WarpProfile.totalCurvature_eq hb.le ?_]
  · rw [hyperbolicPlane_d1]; simp; ring
  · intro r hr
    have : r ≠ 0 := ne_of_gt hr.1
    simpa [Real.sinh_eq_zero] using this

/-! ### The torus of revolution -/

/-- The torus of revolution with tube radius `ρ` and central radius `R`, parametrized by arclength
along the profile circle: `dr² + (R + ρ cos(r/ρ))² dθ²`. -/
noncomputable def torusOfRevolution (R ρ : ℝ) : WarpProfile :=
  ⟨fun r => R + ρ * Real.cos (r / ρ), by fun_prop⟩

@[simp] theorem torusOfRevolution_f (R ρ r : ℝ) :
    (torusOfRevolution R ρ).f r = R + ρ * Real.cos (r / ρ) := rfl

theorem torusOfRevolution_d1 {R ρ : ℝ} (hρ : ρ ≠ 0) :
    (torusOfRevolution R ρ).d1 = fun r => -Real.sin (r / ρ) := by
  refine WarpProfile.d1_eq fun r => ?_
  have h1 : HasDerivAt (fun x : ℝ => x / ρ) (1 / ρ) r := (hasDerivAt_id r).div_const ρ
  have h2 : HasDerivAt (Real.cos ∘ fun x : ℝ => x / ρ) (-Real.sin (r / ρ) * (1 / ρ)) r :=
    (Real.hasDerivAt_cos (r / ρ)).comp r h1
  rw [Function.comp_def] at h2
  have h3 := (h2.const_mul ρ).const_add R
  have h4 : ρ * (-Real.sin (r / ρ) * (1 / ρ)) = -Real.sin (r / ρ) := by field_simp
  rw [h4] at h3
  exact h3

theorem torusOfRevolution_d2 {R ρ : ℝ} (hρ : ρ ≠ 0) :
    (torusOfRevolution R ρ).d2 = fun r => -(Real.cos (r / ρ) / ρ) := by
  refine WarpProfile.d2_eq (torusOfRevolution_d1 hρ) fun r => ?_
  have h1 : HasDerivAt (fun x : ℝ => x / ρ) (1 / ρ) r := (hasDerivAt_id r).div_const ρ
  have h2 : HasDerivAt (Real.sin ∘ fun x : ℝ => x / ρ) (Real.cos (r / ρ) * (1 / ρ)) r :=
    (Real.hasDerivAt_sin (r / ρ)).comp r h1
  rw [Function.comp_def] at h2
  have h3 := h2.neg
  have : -(Real.cos (r / ρ) * (1 / ρ)) = -(Real.cos (r / ρ) / ρ) := by ring
  rw [this] at h3
  exact h3

/-- **The Gaussian curvature of the torus of revolution.** -/
theorem torusOfRevolution_gaussCurvature {R ρ r : ℝ} (hρ : ρ ≠ 0)
    (hf : R + ρ * Real.cos (r / ρ) ≠ 0) :
    (torusOfRevolution R ρ).gaussCurvature r =
      Real.cos (r / ρ) / (ρ * (R + ρ * Real.cos (r / ρ))) := by
  unfold WarpProfile.gaussCurvature
  rw [torusOfRevolution_d2 hρ, torusOfRevolution_f]
  field_simp

/-- **Gauss--Bonnet for the torus of revolution.**  One full period of the profile has total
curvature `0 = 2π·χ(T²)`. -/
theorem torusOfRevolution_totalCurvature {R ρ : ℝ} (hρ : 0 < ρ) (hRρ : ρ < R) :
    (torusOfRevolution R ρ).totalCurvature 0 (2 * π * ρ) = 0 := by
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  have hpi := Real.pi_pos
  have hab : (0 : ℝ) ≤ 2 * π * ρ := by positivity
  have key := WarpProfile.gauss_bonnet_torus_type (W := torusOfRevolution R ρ) hab ?_ ?_
  · rw [key]; ring
  · intro r _
    have hcos : -1 ≤ Real.cos (r / ρ) := Real.neg_one_le_cos _
    have : 0 < R + ρ * Real.cos (r / ρ) := by nlinarith [Real.neg_one_le_cos (r / ρ)]
    simpa using ne_of_gt this
  · rw [torusOfRevolution_d1 hρ']
    have h : 2 * π * ρ / ρ = 2 * π := by field_simp
    simp [h, Real.sin_two_pi]

end GaloisForLFunctions.HTGeometry.GaussBonnet
