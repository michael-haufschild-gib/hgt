import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetCylinder

/-!
# Global recovery of the theory from its anomaly charges

The two anomaly coefficients in arXiv:2611.16364, equation (3.2), determine
the positive scale and subcritical coupling globally. The ratio
`2c/(3c-a)` recovers the discriminant, strengthening local coordinate
independence to an explicit injectivity theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def eulerAnomaly (κ s : ℝ) : ℝ :=
  Real.exp κ * beta (subcriticalCoupling s) ^ 3 * (3 * eta (subcriticalCoupling s) - 2)

def weylAnomaly (κ s : ℝ) : ℝ :=
  Real.exp κ * beta (subcriticalCoupling s) ^ 3 * eta (subcriticalCoupling s)

/-- A linear combination of the anomalies isolates the common positive scale. -/
theorem anomaly_scale (κ s : ℝ) :
    3 * weylAnomaly κ s - eulerAnomaly κ s =
      2 * Real.exp κ * beta (subcriticalCoupling s) ^ 3 := by
  unfold eulerAnomaly weylAnomaly
  ring

theorem anomaly_scale_pos (κ s : ℝ) : 0 < 3 * weylAnomaly κ s - eulerAnomaly κ s := by
  rw [anomaly_scale]
  have h := beta_pos s
  positivity

/-- The anomaly ratio explicitly recovers the vacuum discriminant. -/
theorem anomaly_eta_recovery (κ s : ℝ) :
    2 * weylAnomaly κ s / (3 * weylAnomaly κ s - eulerAnomaly κ s) =
      eta (subcriticalCoupling s) := by
  rw [anomaly_scale]
  unfold weylAnomaly
  field_simp [(beta_pos s).ne']

/-- The same ratio determines the dimensionless coupling. -/
theorem anomaly_coupling_recovery (κ s : ℝ) :
    (1 - (2 * weylAnomaly κ s / (3 * weylAnomaly κ s - eulerAnomaly κ s)) ^ 2) / 4 =
      subcriticalCoupling s := by
  rw [anomaly_eta_recovery, eta_sq]
  rfl

theorem anomaly_scale_recovery (κ s : ℝ) :
    (3 * weylAnomaly κ s - eulerAnomaly κ s) /
      (2 * beta (subcriticalCoupling s) ^ 3) = Real.exp κ := by
  rw [anomaly_scale]
  field_simp [(beta_pos s).ne']

/-- Equality of both anomalies is exactly equality of both independent theory coordinates. -/
theorem anomaly_coordinates_injective (κ s κ' s' : ℝ) :
    eulerAnomaly κ s = eulerAnomaly κ' s' ∧ weylAnomaly κ s = weylAnomaly κ' s' ↔
      κ = κ' ∧ s = s' := by
  constructor
  · rintro ⟨ha, hc⟩
    have he : eta (subcriticalCoupling s) = eta (subcriticalCoupling s') := by
      rw [← anomaly_eta_recovery κ s, ← anomaly_eta_recovery κ' s', ha, hc]
    have hes := congrArg (fun x : ℝ => x ^ 2) he
    rw [eta_sq, eta_sq] at hes
    have hs : s = s' := Real.exp_inj.mp hes
    subst s'
    have hscale : Real.exp κ = Real.exp κ' := by
      rw [← anomaly_scale_recovery κ s, ← anomaly_scale_recovery κ' s, ha, hc]
    exact ⟨Real.exp_inj.mp hscale, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

#print axioms anomaly_coupling_recovery
#print axioms anomaly_coordinates_injective

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
