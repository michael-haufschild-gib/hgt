import GaloisForLFunctions.HTGeometry.GaussBonnetGeodesicCurvature
import GaloisForLFunctions.HTGeometry.GaussBonnetPartialCalculus

/-!
# The Gaussian curvature is the intrinsic sectional curvature

`GaussBonnetOrthogonalPatch` *defines* the Gaussian curvature of the metric `E du² + G dv²` by the
classical orthogonal-coordinate formula

```text
K = -1/(2√(EG)) ( ∂_v(E_v/√(EG)) + ∂_u(G_u/√(EG)) ).
```

This module removes that as an assertion.  It builds the Riemann curvature component

```text
R¹₂₁₂ = ∂_u Γ¹₂₂ - ∂_v Γ¹₁₂ + Γ¹₁₁Γ¹₂₂ + Γ¹₁₂Γ²₂₂ - Γ¹₁₂Γ¹₁₂ - Γ¹₂₂Γ²₁₂
```

directly from the Christoffel symbols of `GaussBonnetGeodesicCurvature`, forms the sectional
curvature `R₁₂₁₂/(EG) = R¹₂₁₂/G`, and proves that it equals the orthogonal-coordinate formula.

Both sides are rational in `E`, `G`, `E_u`, `E_v`, `G_u`, `G_v`, `E_vv`, `G_uu` and `√E`, `√G`; no
mixed second derivative occurs, so no symmetry-of-second-derivatives input is needed.  Together with
`GaussBonnetGeodesicCurvature`, this makes both curvatures in the Gauss--Bonnet identity intrinsic
definitions rather than formulas asserted by fiat.
-/

open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

namespace OrthogonalPatch

variable (M : OrthogonalPatch)

theorem smooth_px_E : ContDiff ℝ ∞ (px M.E) := contDiff_px M.smoothE

theorem smooth_py_E : ContDiff ℝ ∞ (py M.E) := contDiff_py M.smoothE

theorem smooth_px_G : ContDiff ℝ ∞ (px M.G) := contDiff_px M.smoothG

theorem smooth_py_G : ContDiff ℝ ∞ (py M.G) := contDiff_py M.smoothG

theorem twoE_ne (q : ℝ × ℝ) : 2 * M.E q ≠ 0 := by have := M.posE q; positivity

theorem twoG_ne (q : ℝ × ℝ) : 2 * M.G q ≠ 0 := by have := M.posG q; positivity

theorem twoArea_ne (q : ℝ × ℝ) : 2 * M.area q ≠ 0 := by have := M.area_pos q; positivity

/-! ### Derivatives of the basic scalars -/

theorem px_uSpeed (u v : ℝ) :
    px M.uSpeed (u, v) = px M.E (u, v) / (2 * M.uSpeed (u, v)) :=
  px_sqrt M.smoothE (fun q => (M.posE q).ne') u v

theorem py_uSpeed (u v : ℝ) :
    py M.uSpeed (u, v) = py M.E (u, v) / (2 * M.uSpeed (u, v)) :=
  py_sqrt M.smoothE (fun q => (M.posE q).ne') u v

theorem px_vSpeed (u v : ℝ) :
    px M.vSpeed (u, v) = px M.G (u, v) / (2 * M.vSpeed (u, v)) :=
  px_sqrt M.smoothG (fun q => (M.posG q).ne') u v

theorem py_vSpeed (u v : ℝ) :
    py M.vSpeed (u, v) = py M.G (u, v) / (2 * M.vSpeed (u, v)) :=
  py_sqrt M.smoothG (fun q => (M.posG q).ne') u v

theorem px_area_eq (u v : ℝ) :
    px M.area (u, v)
      = px M.E (u, v) / (2 * M.uSpeed (u, v)) * M.vSpeed (u, v)
        + M.uSpeed (u, v) * (px M.G (u, v) / (2 * M.vSpeed (u, v))) := by
  have h : px M.area (u, v)
      = px M.uSpeed (u, v) * M.vSpeed (u, v) + M.uSpeed (u, v) * px M.vSpeed (u, v) :=
    px_mul M.smooth_uSpeed M.smooth_vSpeed u v
  rw [h, M.px_uSpeed u v, M.px_vSpeed u v]

theorem py_area_eq (u v : ℝ) :
    py M.area (u, v)
      = py M.E (u, v) / (2 * M.uSpeed (u, v)) * M.vSpeed (u, v)
        + M.uSpeed (u, v) * (py M.G (u, v) / (2 * M.vSpeed (u, v))) := by
  have h : py M.area (u, v)
      = py M.uSpeed (u, v) * M.vSpeed (u, v) + M.uSpeed (u, v) * py M.vSpeed (u, v) :=
    py_mul M.smooth_uSpeed M.smooth_vSpeed u v
  rw [h, M.py_uSpeed u v, M.py_vSpeed u v]

theorem px_twoArea (u v : ℝ) :
    px (fun q => 2 * M.area q) (u, v) = 2 * px M.area (u, v) := by
  rw [px_mul (A := fun _ : ℝ × ℝ => (2 : ℝ)) contDiff_const M.smooth_area u v, px_const]
  ring

theorem py_twoArea (u v : ℝ) :
    py (fun q => 2 * M.area q) (u, v) = 2 * py M.area (u, v) := by
  rw [py_mul (A := fun _ : ℝ × ℝ => (2 : ℝ)) contDiff_const M.smooth_area u v, py_const]
  ring

theorem px_twoE (u v : ℝ) :
    px (fun q => 2 * M.E q) (u, v) = 2 * px M.E (u, v) := by
  rw [px_mul (A := fun _ : ℝ × ℝ => (2 : ℝ)) contDiff_const M.smoothE u v, px_const]
  ring

theorem py_twoE (u v : ℝ) :
    py (fun q => 2 * M.E q) (u, v) = 2 * py M.E (u, v) := by
  rw [py_mul (A := fun _ : ℝ × ℝ => (2 : ℝ)) contDiff_const M.smoothE u v, py_const]
  ring

/-! ### Derivatives of the Liouville form and the Christoffel symbols -/

theorem px_P_eq (u v : ℝ) :
    px M.P (u, v)
      = (px (px M.G) (u, v) * (2 * M.area (u, v)) - px M.G (u, v) * (2 * px M.area (u, v)))
        / (2 * M.area (u, v)) ^ 2 := by
  have h := px_div (A := px M.G) (B := fun q => 2 * M.area q) M.smooth_px_G
    (contDiff_const.mul M.smooth_area) M.twoArea_ne u v
  rw [show M.P = fun q => px M.G q / (2 * M.area q) from rfl, h, M.px_twoArea u v]

theorem py_Q_eq (u v : ℝ) :
    py M.Q (u, v)
      = (py (py M.E) (u, v) * (2 * M.area (u, v)) - py M.E (u, v) * (2 * py M.area (u, v)))
        / (2 * M.area (u, v)) ^ 2 := by
  have h := py_div (A := py M.E) (B := fun q => 2 * M.area q) M.smooth_py_E
    (contDiff_const.mul M.smooth_area) M.twoArea_ne u v
  rw [show M.Q = fun q => py M.E q / (2 * M.area q) from rfl, h, M.py_twoArea u v]

theorem px_chr122_eq (u v : ℝ) :
    px M.chr122 (u, v)
      = (-px (px M.G) (u, v) * (2 * M.E (u, v)) - -px M.G (u, v) * (2 * px M.E (u, v)))
        / (2 * M.E (u, v)) ^ 2 := by
  have h := px_div (A := fun q => -px M.G q) (B := fun q => 2 * M.E q) M.smooth_px_G.neg
    (contDiff_const.mul M.smoothE) M.twoE_ne u v
  rw [show M.chr122 = fun q => -px M.G q / (2 * M.E q) from rfl, h, M.px_twoE u v,
    px_neg M.smooth_px_G u v]

theorem py_chr112_eq (u v : ℝ) :
    py M.chr112 (u, v)
      = (py (py M.E) (u, v) * (2 * M.E (u, v)) - py M.E (u, v) * (2 * py M.E (u, v)))
        / (2 * M.E (u, v)) ^ 2 := by
  have h := py_div (A := py M.E) (B := fun q => 2 * M.E q) M.smooth_py_E
    (contDiff_const.mul M.smoothE) M.twoE_ne u v
  rw [show M.chr112 = fun q => py M.E q / (2 * M.E q) from rfl, h, M.py_twoE u v]

/-! ### The Riemann tensor and the sectional curvature -/

/-- The Riemann curvature component `R¹₂₁₂` of the orthogonal metric, computed from its Christoffel
symbols. -/
noncomputable def riemannUpper (p : ℝ × ℝ) : ℝ :=
  px M.chr122 p - py M.chr112 p
    + M.chr111 p * M.chr122 p + M.chr112 p * M.chr222 p
    - M.chr112 p * M.chr112 p - M.chr122 p * M.chr212 p

/-- The **intrinsic sectional curvature** `R₁₂₁₂/(EG) = R¹₂₁₂/G`. -/
noncomputable def sectionalCurvature (p : ℝ × ℝ) : ℝ := M.riemannUpper p / M.G p

/-- **The Gaussian curvature is the intrinsic sectional curvature.**  The orthogonal-coordinate
formula used throughout the Gauss--Bonnet development agrees with the curvature computed from the
Riemann tensor of the Levi-Civita connection. -/
theorem sectionalCurvature_eq_gaussCurvature (u v : ℝ) :
    M.sectionalCurvature (u, v) = M.gaussCurvature (u, v) := by
  have hs : M.uSpeed (u, v) ≠ 0 := (M.uSpeed_pos (u, v)).ne'
  have ht : M.vSpeed (u, v) ≠ 0 := (M.vSpeed_pos (u, v)).ne'
  have hE : M.E (u, v) = M.uSpeed (u, v) ^ 2 := (M.uSpeed_sq (u, v)).symm
  have hG : M.G (u, v) = M.vSpeed (u, v) ^ 2 := (M.vSpeed_sq (u, v)).symm
  have hA : M.area (u, v) = M.uSpeed (u, v) * M.vSpeed (u, v) := rfl
  unfold sectionalCurvature riemannUpper gaussCurvature
  rw [M.px_chr122_eq u v, M.py_chr112_eq u v, M.px_P_eq u v, M.py_Q_eq u v,
    M.px_area_eq u v, M.py_area_eq u v]
  unfold chr111 chr112 chr122 chr222 chr212
  rw [hA, hE, hG]
  field_simp
  ring

end OrthogonalPatch

end GaloisForLFunctions.HTGeometry.GaussBonnet
