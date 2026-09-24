import GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationSign
import GaloisForLFunctions.RHTower.CothInfra

namespace RHTower
noncomputable section

/-- Exact aperture slack discarded by the source-only flux lower bound. -/
theorem deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack (a r : ℝ) :
    deriv (thetaCuspCenterCompensationFlux a) r =
      r * Real.sinh (a * r) * thetaCuspCenterCompensationSource (r / 2) +
      r * thetaCuspFullSource (r / 2) ^ (2 : ℕ) *
        (a * r * Real.cosh (a * r) - Real.sinh (a * r)) := by
  rw [(hasDerivAt_thetaCuspCenterCompensationFlux a r).deriv]
  unfold thetaCuspCenterCompensationSource
  ring

/-- The literal zero-integral flux remains strictly positive where its coarse source vanishes. -/
theorem deriv_thetaCuspCenterCompensationFlux_pos_at_source_zero
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hz : thetaCuspCenterCompensationSource (r / 2) = 0) :
    0 < deriv (thetaCuspCenterCompensationFlux a) r := by
  rw [deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack, hz, mul_zero, zero_add]
  have hs : 0 < a * r * Real.cosh (a * r) - Real.sinh (a * r) :=
    sub_pos.mpr (sinh_lt_mul_cosh (mul_pos ha hr))
  exact mul_pos (mul_pos hr (sq_pos_of_pos (thetaCuspFullSource_pos_all (r / 2)))) hs

/-- The unique coarse-source transition is not a zero of the actual aperture flux. -/
theorem exists_thetaCuspCenterCompensationFlux_transition_pos :
    ∃ τ : ℝ, 0 < τ ∧ thetaCuspCenterCompensationSource τ = 0 ∧
      ∀ a : ℝ, 0 < a → 0 < deriv (thetaCuspCenterCompensationFlux a) (2 * τ) := by
  obtain ⟨τ, hτ, hs⟩ := exists_thetaCuspCenterCompensationSource_transition
  have hzero : thetaCuspCenterCompensationSource τ = 0 :=
    (hs τ hτ.le).2.1.mpr rfl
  refine ⟨τ, hτ, hzero, ?_⟩
  intro a ha
  have hr : 0 < 2 * τ := by positivity
  have hhalf : (2 * τ) / 2 = τ := by ring
  exact deriv_thetaCuspCenterCompensationFlux_pos_at_source_zero ha hr
    (by simpa [hhalf] using hzero)

end
end RHTower
