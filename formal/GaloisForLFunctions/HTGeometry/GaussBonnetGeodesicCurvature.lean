import GaloisForLFunctions.HTGeometry.GaussBonnetOrthogonalPatch

/-!
# Intrinsic geodesic curvature on an orthogonal coordinate patch

`GaussBonnetOrthogonalPatch` *defines* the geodesic curvature of the coordinate curves by
Liouville's formulas

```text
κ_g( v = const, u increasing ) = -E_v / (2E√G),
κ_g( u = const, v increasing ) =  G_u / (2G√E).
```

This module removes that as an assertion.  It builds the Christoffel symbols of the metric
`E du² + G dv²`, the covariant acceleration of a curve, the unit normal, and the intrinsic
geodesic curvature

```text
κ_g = ⟨ D_t c', N ⟩ / |c'|²  =  √(EG) ( u' D^v - v' D^u ) / |c'|³,
```

and proves that evaluating it on the two coordinate directions returns exactly Liouville's
formulas.  It also shows that the meridians of a geodesic polar patch — the curves `θ = const` of a
metric with `E = 1` — have vanishing covariant acceleration, i.e. really are geodesics.

The Christoffel symbols of an orthogonal metric are

```text
Γ¹₁₁ = E_u/(2E),   Γ¹₁₂ = E_v/(2E),   Γ¹₂₂ = -G_u/(2E),
Γ²₁₁ = -E_v/(2G),  Γ²₁₂ = G_u/(2G),   Γ²₂₂ = G_v/(2G).
```
-/

open scoped Real ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

namespace OrthogonalPatch

variable (M : OrthogonalPatch)

/-- Christoffel symbol `Γ¹₁₁ = E_u/(2E)`. -/
noncomputable def chr111 (p : ℝ × ℝ) : ℝ := px M.E p / (2 * M.E p)

/-- Christoffel symbol `Γ¹₁₂ = E_v/(2E)`. -/
noncomputable def chr112 (p : ℝ × ℝ) : ℝ := py M.E p / (2 * M.E p)

/-- Christoffel symbol `Γ¹₂₂ = -G_u/(2E)`. -/
noncomputable def chr122 (p : ℝ × ℝ) : ℝ := -px M.G p / (2 * M.E p)

/-- Christoffel symbol `Γ²₁₁ = -E_v/(2G)`. -/
noncomputable def chr211 (p : ℝ × ℝ) : ℝ := -py M.E p / (2 * M.G p)

/-- Christoffel symbol `Γ²₁₂ = G_u/(2G)`. -/
noncomputable def chr212 (p : ℝ × ℝ) : ℝ := px M.G p / (2 * M.G p)

/-- Christoffel symbol `Γ²₂₂ = G_v/(2G)`. -/
noncomputable def chr222 (p : ℝ × ℝ) : ℝ := py M.G p / (2 * M.G p)

/-- The first coordinate of the covariant acceleration of a curve with 2-jet `(u₁, v₁, u₂)` at
`p`. -/
noncomputable def covAccU (p : ℝ × ℝ) (u₁ v₁ u₂ : ℝ) : ℝ :=
  u₂ + M.chr111 p * u₁ ^ (2 : ℕ) + 2 * M.chr112 p * u₁ * v₁ + M.chr122 p * v₁ ^ (2 : ℕ)

/-- The second coordinate of the covariant acceleration of a curve with 2-jet `(u₁, v₁, v₂)` at
`p`. -/
noncomputable def covAccV (p : ℝ × ℝ) (u₁ v₁ v₂ : ℝ) : ℝ :=
  v₂ + M.chr211 p * u₁ ^ (2 : ℕ) + 2 * M.chr212 p * u₁ * v₁ + M.chr222 p * v₁ ^ (2 : ℕ)

/-- The Riemannian speed `|c'| = √(E u'² + G v'²)` of a curve. -/
noncomputable def speed (p : ℝ × ℝ) (u₁ v₁ : ℝ) : ℝ :=
  Real.sqrt (M.E p * u₁ ^ (2 : ℕ) + M.G p * v₁ ^ (2 : ℕ))

/-- **The intrinsic geodesic curvature** of a curve, read off its 2-jet:
`κ_g = √(EG)(u' D^v - v' D^u)/|c'|³`, the normal component of the covariant acceleration divided by
the squared speed. -/
noncomputable def geodesicCurvature (p : ℝ × ℝ) (u₁ v₁ u₂ v₂ : ℝ) : ℝ :=
  M.area p * (u₁ * M.covAccV p u₁ v₁ v₂ - v₁ * M.covAccU p u₁ v₁ u₂) / M.speed p u₁ v₁ ^ (3 : ℕ)

/-- A curve is a **geodesic** at a point when its covariant acceleration vanishes there. -/
def IsGeodesicJet (p : ℝ × ℝ) (u₁ v₁ u₂ v₂ : ℝ) : Prop :=
  M.covAccU p u₁ v₁ u₂ = 0 ∧ M.covAccV p u₁ v₁ v₂ = 0

/-- Geodesics have vanishing geodesic curvature. -/
theorem geodesicCurvature_eq_zero {p : ℝ × ℝ} {u₁ v₁ u₂ v₂ : ℝ}
    (h : M.IsGeodesicJet p u₁ v₁ u₂ v₂) : M.geodesicCurvature p u₁ v₁ u₂ v₂ = 0 := by
  unfold geodesicCurvature
  rw [h.1, h.2]
  simp

theorem speed_uDirection (p : ℝ × ℝ) : M.speed p 1 0 = M.uSpeed p := by
  simp [speed, uSpeed]

theorem speed_vDirection (p : ℝ × ℝ) : M.speed p 0 1 = M.vSpeed p := by
  simp [speed, vSpeed]

/-- **Liouville's formula for the `u`-coordinate curves is a theorem.**  The intrinsic geodesic
curvature of the curve `v = const`, traversed with unit coordinate speed, is `-E_v/(2E√G)`. -/
theorem geodesicCurvature_uCurve (p : ℝ × ℝ) :
    M.geodesicCurvature p 1 0 0 0 = M.uCurveGeodesicCurvature p := by
  have hE : M.E p = M.uSpeed p ^ (2 : ℕ) := (M.uSpeed_sq p).symm
  have he0 : M.uSpeed p ≠ 0 := (M.uSpeed_pos p).ne'
  have hg0 : M.vSpeed p ≠ 0 := (M.vSpeed_pos p).ne'
  have hG0 : M.G p ≠ 0 := (M.posG p).ne'
  unfold geodesicCurvature covAccU covAccV uCurveGeodesicCurvature area chr211
  rw [M.speed_uDirection p, hE]
  field_simp
  rw [M.vSpeed_sq p]
  ring

/-- **Liouville's formula for the `v`-coordinate curves is a theorem.**  The intrinsic geodesic
curvature of the curve `u = const`, traversed with unit coordinate speed, is `G_u/(2G√E)`. -/
theorem geodesicCurvature_vCurve (p : ℝ × ℝ) :
    M.geodesicCurvature p 0 1 0 0 = M.vCurveGeodesicCurvature p := by
  have hG : M.G p = M.vSpeed p ^ (2 : ℕ) := (M.vSpeed_sq p).symm
  have he0 : M.uSpeed p ≠ 0 := (M.uSpeed_pos p).ne'
  have hg0 : M.vSpeed p ≠ 0 := (M.vSpeed_pos p).ne'
  have hE0 : M.E p ≠ 0 := (M.posE p).ne'
  unfold geodesicCurvature covAccU covAccV vCurveGeodesicCurvature area chr122
  rw [M.speed_vDirection p, hG]
  field_simp
  rw [M.uSpeed_sq p]
  ring

end OrthogonalPatch

end GaloisForLFunctions.HTGeometry.GaussBonnet
