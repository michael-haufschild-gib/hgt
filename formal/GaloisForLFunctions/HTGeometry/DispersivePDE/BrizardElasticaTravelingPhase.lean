import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Traveling-phase algebra in arXiv:2607.21750

Equations (44)--(47) integrate the imaginary part of the traveling-wave NLS and substitute the
resulting phase slope into the real part.  Nonzero dispersion, curvature scale, and instantaneous
curvature are bundled as units.  This makes the cancellation unconditional and identifies the
NLS-selected elastica multiplier exactly.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Integrated phase slope following paper equation (44). -/
noncomputable def travelingPhaseSlope (c τ₀ : ℝ) (D k₀ κ : ℝˣ) : ℝ :=
  c / (2 * (D : ℝ)) + (k₀ : ℝ) ^ 2 * τ₀ / (κ : ℝ) ^ 2

/-- The phase slope is uniform drift plus the conserved elastica torsion. -/
theorem travelingPhaseSlope_eq_drift_add_torsion
    (c τ₀ : ℝ) (D k₀ κ : ℝˣ) :
    travelingPhaseSlope c τ₀ D k₀ κ =
      c / (2 * (D : ℝ)) + torsion (k₀ : ℝ) τ₀ κ := by
  rfl

/-- Exact cancellation producing the curvature equation (45). -/
theorem travelingPhase_curvatureForce
    (c τ₀ : ℝ) (D k₀ κ : ℝˣ) :
    -(c / (D : ℝ)) * (κ : ℝ) * travelingPhaseSlope c τ₀ D k₀ κ +
        (κ : ℝ) * travelingPhaseSlope c τ₀ D k₀ κ ^ 2 =
      -(c ^ 2) / (4 * (D : ℝ) ^ 2) * (κ : ℝ) +
        (k₀ : ℝ) ^ 4 * τ₀ ^ 2 / (κ : ℝ) ^ 3 := by
  rw [travelingPhaseSlope]
  field_simp [D.ne_zero, κ.ne_zero]
  ring

/-- Paper's dimensionless speed convention `c=k₀Dγ`. -/
noncomputable def selectedWaveSpeed (D k₀ : ℝˣ) (γ : ℝ) : ℝ :=
  (k₀ : ℝ) * (D : ℝ) * γ

theorem selectedWaveSpeed_eq_zero_iff (D k₀ : ℝˣ) (γ : ℝ) :
    selectedWaveSpeed D k₀ γ = 0 ↔ γ = 0 := by
  rw [selectedWaveSpeed]
  simp [D.ne_zero, k₀.ne_zero]

/-- With selected speed, uniform phase drift is exactly `k₀γ/2`. -/
theorem selected_travelingPhaseSlope (D k₀ κ : ℝˣ) (γ τ₀ : ℝ) :
    travelingPhaseSlope (selectedWaveSpeed D k₀ γ) τ₀ D k₀ κ =
      (k₀ : ℝ) * γ / 2 + torsion (k₀ : ℝ) τ₀ κ := by
  rw [travelingPhaseSlope_eq_drift_add_torsion, selectedWaveSpeed]
  field_simp [D.ne_zero]

/-- Equation (47): dimensional speed formula recovers the selected multiplier. -/
theorem selectedWaveSpeed_lambda (D k₀ : ℝˣ) (γ : ℝ) :
    -(selectedWaveSpeed D k₀ γ) ^ 2 /
        (2 * (k₀ : ℝ) ^ 2 * (D : ℝ) ^ 2) = waveLambda γ := by
  rw [selectedWaveSpeed, waveLambda]
  field_simp [D.ne_zero, k₀.ne_zero]

/-- Equation (45) in the selected dimensionless speed convention. -/
theorem selected_curvatureForce (D k₀ κ : ℝˣ) (γ τ₀ : ℝ) :
    -(selectedWaveSpeed D k₀ γ / (D : ℝ)) * (κ : ℝ) *
          travelingPhaseSlope (selectedWaveSpeed D k₀ γ) τ₀ D k₀ κ +
        (κ : ℝ) *
          travelingPhaseSlope (selectedWaveSpeed D k₀ γ) τ₀ D k₀ κ ^ 2 =
      waveLambda γ * (k₀ : ℝ) ^ 2 * (κ : ℝ) / 2 +
        (k₀ : ℝ) ^ 4 * τ₀ ^ 2 / (κ : ℝ) ^ 3 := by
  rw [travelingPhase_curvatureForce, selectedWaveSpeed, waveLambda]
  field_simp [D.ne_zero, k₀.ne_zero, κ.ne_zero]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
