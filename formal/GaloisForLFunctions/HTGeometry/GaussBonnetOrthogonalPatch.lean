import GaloisForLFunctions.HTGeometry.GaussBonnetPlanarPartials

/-!
# Local Gauss--Bonnet on an orthogonal coordinate patch

An **orthogonal coordinate patch** is a Riemannian metric

```text
g = E(u,v) du² + G(u,v) dv²
```

on the plane, with `E` and `G` smooth and positive.  Its Gaussian curvature is given by the
classical orthogonal-coordinate formula

```text
K = -1/(2√(EG)) · ( ∂_v( E_v/√(EG) ) + ∂_u( G_u/√(EG) ) ),
```

its area element is `dA = √(EG) du dv`, and Liouville's formula gives the geodesic curvature of the
coordinate curves:

```text
κ_g( v = const, u increasing ) = -E_v / (2E√G),
κ_g( u = const, v increasing ) =  G_u / (2G√E).
```

Writing `P = G_u/(2√(EG))` and `Q = E_v/(2√(EG))`, the curvature formula says exactly

```text
K √(EG) = -( ∂_u P + ∂_v Q ),
```

while Liouville's formula says exactly that the arclength forms of the geodesic curvature along the
four sides of a coordinate rectangle are `∓Q du` and `±P dv`.  Green's theorem — here in its
elementary two-variable form, the fundamental theorem of calculus in each variable together with
Fubini — therefore gives

```text
∫∫_R K dA + ∮_{∂R} κ_g ds = 0,
```

and since the coordinate curves are orthogonal, the four corners contribute exterior angles `π/2`
each, so

```text
∫∫_R K dA + ∮_{∂R} κ_g ds + Σ exterior angles = 2π = 2π · χ(disc).
```

This is the local Gauss--Bonnet theorem.  Everything below is unconditional.
-/

open MeasureTheory intervalIntegral
open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- An **orthogonal coordinate patch**: the Riemannian metric `E du² + G dv²` on the plane,
with smooth positive coefficients. -/
structure OrthogonalPatch where
  /-- The `du²` coefficient of the first fundamental form. -/
  E : ℝ × ℝ → ℝ
  /-- The `dv²` coefficient of the first fundamental form. -/
  G : ℝ × ℝ → ℝ
  /-- `E` is smooth. -/
  smoothE : ContDiff ℝ ∞ E
  /-- `G` is smooth. -/
  smoothG : ContDiff ℝ ∞ G
  /-- `E` is positive: the metric is Riemannian. -/
  posE : ∀ p, 0 < E p
  /-- `G` is positive: the metric is Riemannian. -/
  posG : ∀ p, 0 < G p

namespace OrthogonalPatch

variable (M : OrthogonalPatch)

/-- `√E`: the speed of the coordinate curve `v = const`. -/
noncomputable def uSpeed (p : ℝ × ℝ) : ℝ := Real.sqrt (M.E p)

/-- `√G`: the speed of the coordinate curve `u = const`. -/
noncomputable def vSpeed (p : ℝ × ℝ) : ℝ := Real.sqrt (M.G p)

/-- The Riemannian area density `√(EG)`. -/
noncomputable def area (p : ℝ × ℝ) : ℝ := M.uSpeed p * M.vSpeed p

theorem uSpeed_pos (p : ℝ × ℝ) : 0 < M.uSpeed p := Real.sqrt_pos.mpr (M.posE p)

theorem vSpeed_pos (p : ℝ × ℝ) : 0 < M.vSpeed p := Real.sqrt_pos.mpr (M.posG p)

theorem area_pos (p : ℝ × ℝ) : 0 < M.area p := mul_pos (M.uSpeed_pos p) (M.vSpeed_pos p)

theorem uSpeed_sq (p : ℝ × ℝ) : M.uSpeed p ^ 2 = M.E p := Real.sq_sqrt (M.posE p).le

theorem vSpeed_sq (p : ℝ × ℝ) : M.vSpeed p ^ 2 = M.G p := Real.sq_sqrt (M.posG p).le

theorem area_eq_sqrt (p : ℝ × ℝ) : M.area p = Real.sqrt (M.E p * M.G p) :=
  (Real.sqrt_mul (M.posE p).le _).symm

theorem smooth_uSpeed : ContDiff ℝ ∞ M.uSpeed := M.smoothE.sqrt fun p => (M.posE p).ne'

theorem smooth_vSpeed : ContDiff ℝ ∞ M.vSpeed := M.smoothG.sqrt fun p => (M.posG p).ne'

theorem smooth_area : ContDiff ℝ ∞ M.area := M.smooth_uSpeed.mul M.smooth_vSpeed

/-- The `dv` component `G_u/(2√(EG))` of the Liouville one-form. -/
noncomputable def P (p : ℝ × ℝ) : ℝ := px M.G p / (2 * M.area p)

/-- The `du` component `E_v/(2√(EG))` of the Liouville one-form. -/
noncomputable def Q (p : ℝ × ℝ) : ℝ := py M.E p / (2 * M.area p)

theorem smooth_P : ContDiff ℝ ∞ M.P :=
  (contDiff_px M.smoothG).div (contDiff_const.mul M.smooth_area)
    fun p => by have := M.area_pos p; positivity

theorem smooth_Q : ContDiff ℝ ∞ M.Q :=
  (contDiff_py M.smoothE).div (contDiff_const.mul M.smooth_area)
    fun p => by have := M.area_pos p; positivity

/-- **The Gaussian curvature** of the orthogonal metric `E du² + G dv²`,
`K = -1/(2√(EG)) ( ∂_v(E_v/√(EG)) + ∂_u(G_u/√(EG)) )`. -/
noncomputable def gaussCurvature (p : ℝ × ℝ) : ℝ := -(px M.P p + py M.Q p) / M.area p

/-- The curvature density `K √(EG)`: the integrand of `∫∫ K dA` in the coordinates `(u,v)`. -/
noncomputable def curvatureDensity (p : ℝ × ℝ) : ℝ := -(px M.P p + py M.Q p)

theorem curvatureDensity_eq_mul (p : ℝ × ℝ) :
    M.curvatureDensity p = M.gaussCurvature p * M.area p := by
  have h := (M.area_pos p).ne'
  unfold curvatureDensity gaussCurvature
  field_simp

/-- **Liouville's formula** for the coordinate curve `v = const`, traversed with increasing `u`. -/
noncomputable def uCurveGeodesicCurvature (p : ℝ × ℝ) : ℝ :=
  -py M.E p / (2 * M.E p * M.vSpeed p)

/-- **Liouville's formula** for the coordinate curve `u = const`, traversed with increasing `v`. -/
noncomputable def vCurveGeodesicCurvature (p : ℝ × ℝ) : ℝ :=
  px M.G p / (2 * M.G p * M.uSpeed p)

/-- The arclength form of the geodesic curvature along a `u`-coordinate curve is `-Q du`. -/
theorem uCurve_kappa_mul_speed (p : ℝ × ℝ) :
    M.uCurveGeodesicCurvature p * M.uSpeed p = -M.Q p := by
  have he : M.E p = M.uSpeed p ^ 2 := (M.uSpeed_sq p).symm
  have he0 : M.uSpeed p ≠ 0 := (M.uSpeed_pos p).ne'
  have hg0 : M.vSpeed p ≠ 0 := (M.vSpeed_pos p).ne'
  unfold uCurveGeodesicCurvature Q area
  rw [he]
  field_simp

/-- The arclength form of the geodesic curvature along a `v`-coordinate curve is `P dv`. -/
theorem vCurve_kappa_mul_speed (p : ℝ × ℝ) :
    M.vCurveGeodesicCurvature p * M.vSpeed p = M.P p := by
  have hg : M.G p = M.vSpeed p ^ 2 := (M.vSpeed_sq p).symm
  have he0 : M.uSpeed p ≠ 0 := (M.uSpeed_pos p).ne'
  have hg0 : M.vSpeed p ≠ 0 := (M.vSpeed_pos p).ne'
  unfold vCurveGeodesicCurvature P area
  rw [hg]
  field_simp

/-- `∫∫_R K dA` over the coordinate rectangle `[a,b] × [c,d]`. -/
noncomputable def totalCurvature (a b c d : ℝ) : ℝ :=
  ∫ v in c..d, ∫ u in a..b, M.gaussCurvature (u, v) * M.area (u, v)

/-- `∮_{∂R} κ_g ds` along the positively oriented boundary of the coordinate rectangle
`[a,b] × [c,d]`: bottom left-to-right, right side upwards, top right-to-left, left side
downwards. -/
noncomputable def boundaryTurning (a b c d : ℝ) : ℝ :=
  (∫ u in a..b, M.uCurveGeodesicCurvature (u, c) * M.uSpeed (u, c))
    + (∫ v in c..d, M.vCurveGeodesicCurvature (b, v) * M.vSpeed (b, v))
    - (∫ u in a..b, M.uCurveGeodesicCurvature (u, d) * M.uSpeed (u, d))
    - (∫ v in c..d, M.vCurveGeodesicCurvature (a, v) * M.vSpeed (a, v))

/-! ### The Green computation -/

theorem integral_px_P (v a b : ℝ) :
    (∫ u in a..b, px M.P (u, v)) = M.P (b, v) - M.P (a, v) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_px M.smooth_P u v)
    ((continuous_sliceFst (continuous_px M.smooth_P) v).intervalIntegrable a b)

theorem integral_py_Q (u c d : ℝ) :
    (∫ v in c..d, py M.Q (u, v)) = M.Q (u, d) - M.Q (u, c) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_py M.smooth_Q u v)
    ((continuous_sliceSnd (continuous_py M.smooth_Q) u).intervalIntegrable c d)

theorem inner_curvatureDensity (v a b : ℝ) :
    (∫ u in a..b, M.curvatureDensity (u, v))
      = -((M.P (b, v) - M.P (a, v)) + ∫ u in a..b, py M.Q (u, v)) := by
  have h1 : IntervalIntegrable (fun u : ℝ => px M.P (u, v)) volume a b :=
    (continuous_sliceFst (continuous_px M.smooth_P) v).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun u : ℝ => py M.Q (u, v)) volume a b :=
    (continuous_sliceFst (continuous_py M.smooth_Q) v).intervalIntegrable a b
  simp only [curvatureDensity]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_add h1 h2, integral_px_P]

theorem continuous_inner_py_Q (a b : ℝ) :
    Continuous fun v : ℝ => ∫ u in a..b, py M.Q (u, v) := by
  have hcont : Continuous (Function.uncurry fun (v : ℝ) (u : ℝ) => py M.Q (u, v)) := by
    have := continuous_py M.smooth_Q
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont a b

/-- **The Green identity behind Gauss--Bonnet.**  The total curvature of a coordinate rectangle is
minus the boundary integral of the Liouville one-form. -/
theorem totalCurvature_eq (a b c d : ℝ) :
    M.totalCurvature a b c d
      = -((∫ v in c..d, M.P (b, v) - M.P (a, v)) + ∫ u in a..b, M.Q (u, d) - M.Q (u, c)) := by
  have hcong : M.totalCurvature a b c d = ∫ v in c..d, ∫ u in a..b, M.curvatureDensity (u, v) := by
    unfold totalCurvature
    refine intervalIntegral.integral_congr fun v _ => ?_
    exact intervalIntegral.integral_congr fun u _ => (M.curvatureDensity_eq_mul (u, v)).symm
  rw [hcong]
  have hstep : (∫ v in c..d, ∫ u in a..b, M.curvatureDensity (u, v))
      = ∫ v in c..d, -((M.P (b, v) - M.P (a, v)) + ∫ u in a..b, py M.Q (u, v)) :=
    intervalIntegral.integral_congr fun v _ => M.inner_curvatureDensity v a b
  rw [hstep]
  have hI1 : IntervalIntegrable (fun v : ℝ => M.P (b, v) - M.P (a, v)) volume c d :=
    (((continuous_sliceSnd M.smooth_P.continuous b).sub
      (continuous_sliceSnd M.smooth_P.continuous a))).intervalIntegrable c d
  have hI2 : IntervalIntegrable (fun v : ℝ => ∫ u in a..b, py M.Q (u, v)) volume c d :=
    (M.continuous_inner_py_Q a b).intervalIntegrable c d
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_add hI1 hI2]
  have hswap : (∫ v in c..d, ∫ u in a..b, py M.Q (u, v))
      = ∫ u in a..b, ∫ v in c..d, py M.Q (u, v) := by
    refine intervalIntegral_swap ?_ c d a b
    have := continuous_py M.smooth_Q
    fun_prop
  rw [hswap]
  congr 2
  exact intervalIntegral.integral_congr fun u _ => M.integral_py_Q u c d

theorem boundaryTurning_eq (a b c d : ℝ) :
    M.boundaryTurning a b c d
      = (∫ v in c..d, M.P (b, v) - M.P (a, v)) + ∫ u in a..b, M.Q (u, d) - M.Q (u, c) := by
  have hQc : IntervalIntegrable (fun u : ℝ => M.Q (u, c)) volume a b :=
    (continuous_sliceFst M.smooth_Q.continuous c).intervalIntegrable a b
  have hQd : IntervalIntegrable (fun u : ℝ => M.Q (u, d)) volume a b :=
    (continuous_sliceFst M.smooth_Q.continuous d).intervalIntegrable a b
  have hPa : IntervalIntegrable (fun v : ℝ => M.P (a, v)) volume c d :=
    (continuous_sliceSnd M.smooth_P.continuous a).intervalIntegrable c d
  have hPb : IntervalIntegrable (fun v : ℝ => M.P (b, v)) volume c d :=
    (continuous_sliceSnd M.smooth_P.continuous b).intervalIntegrable c d
  unfold boundaryTurning
  rw [intervalIntegral.integral_sub hPb hPa, intervalIntegral.integral_sub hQd hQc]
  have e1 : (∫ u in a..b, M.uCurveGeodesicCurvature (u, c) * M.uSpeed (u, c))
      = -∫ u in a..b, M.Q (u, c) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ => M.uCurve_kappa_mul_speed (u, c)
  have e2 : (∫ u in a..b, M.uCurveGeodesicCurvature (u, d) * M.uSpeed (u, d))
      = -∫ u in a..b, M.Q (u, d) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ => M.uCurve_kappa_mul_speed (u, d)
  have e3 : (∫ v in c..d, M.vCurveGeodesicCurvature (b, v) * M.vSpeed (b, v))
      = ∫ v in c..d, M.P (b, v) :=
    intervalIntegral.integral_congr fun v _ => M.vCurve_kappa_mul_speed (b, v)
  have e4 : (∫ v in c..d, M.vCurveGeodesicCurvature (a, v) * M.vSpeed (a, v))
      = ∫ v in c..d, M.P (a, v) :=
    intervalIntegral.integral_congr fun v _ => M.vCurve_kappa_mul_speed (a, v)
  rw [e1, e2, e3, e4]
  ring

/-- **Gauss--Bonnet, analytic core.**  On every coordinate rectangle of every smooth orthogonal
Riemannian metric, the total curvature and the total geodesic turning of the boundary cancel. -/
theorem totalCurvature_add_boundaryTurning (a b c d : ℝ) :
    M.totalCurvature a b c d + M.boundaryTurning a b c d = 0 := by
  rw [M.totalCurvature_eq a b c d, M.boundaryTurning_eq a b c d]
  ring

/-- **Local Gauss--Bonnet on a coordinate rectangle.**

```text
∫∫_R K dA + ∮_{∂R} κ_g ds + Σ (exterior angles) = 2π = 2π·χ(disc),
```

with the four exterior angles equal to `π/2` because the coordinate curves of an orthogonal patch
meet at right angles. -/
theorem gauss_bonnet_rectangle (a b c d : ℝ) :
    M.totalCurvature a b c d + M.boundaryTurning a b c d + 4 * (π / 2) = 2 * π := by
  rw [M.totalCurvature_add_boundaryTurning a b c d]
  ring

end OrthogonalPatch

end GaloisForLFunctions.HTGeometry.GaussBonnet
