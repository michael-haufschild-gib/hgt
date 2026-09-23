import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHausdorffSource
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionCDDExpansion

/-!
# Erased information as an endpoint CDD contribution

The zero-rate energy contributes the flat-JT phase ray. All higher coefficients
remain the actual full collision moments on the common convergence interval.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

def egbFixedChargeAGibbsFullCollisionCDDPhase (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (θ : ℝ) : ℝ :=
  hausdorffCDDPhase (egbFixedChargeAGibbsFullCollisionHausdorffSource n β E) θ

/-- The full phase splits into an erased-information endpoint ray and two surviving shell phases. -/
theorem egbFixedChargeAGibbsFullCollisionCDDPhase_formula (n : ℕ) (β θ : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionCDDPhase n β E θ =
      8 * egbFixedChargeAGibbsDiscardedModeEnergy n β E * Real.sinh θ +
      egbFixedChargeAGibbsSlowModeEnergy n β E * cddPhaseKernel (4 / 9) θ +
      egbFixedChargeAGibbsFastModeEnergy n β E * cddPhaseKernel (1 / 36) θ := by
  rw [egbFixedChargeAGibbsFullCollisionCDDPhase, egbFixedChargeAGibbsFullCollisionHausdorffSource,
    hausdorffCDDPhase_add, hausdorffCDDPhase_add,
    hausdorffCDDPhase_atom, hausdorffCDDPhase_atom, hausdorffCDDPhase_atom]
  change egbFixedChargeAGibbsDiscardedModeEnergy n β E * cddPhaseKernel 0 θ +
    egbFixedChargeAGibbsSlowModeEnergy n β E * cddPhaseKernel (4 / 9) θ +
    egbFixedChargeAGibbsFastModeEnergy n β E * cddPhaseKernel (1 / 36) θ = _
  rw [cddPhaseKernel_zero]
  ring

/-- The complete phase has a closed form with one hyperbolic-sine term and two arctangents. -/
theorem egbFixedChargeAGibbsFullCollisionCDDPhase_arctan (n : ℕ) (β θ : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionCDDPhase n β E θ =
      8 * egbFixedChargeAGibbsDiscardedModeEnergy n β E * Real.sinh θ +
      6 * egbFixedChargeAGibbsSlowModeEnergy n β E * Real.arctan ((12 / 13 : ℝ) * Real.sinh θ) +
      24 * egbFixedChargeAGibbsFastModeEnergy n β E * Real.arctan ((12 / 37 : ℝ) * Real.sinh θ) := by
  have hr := cddPhaseKernel_sq (by norm_num : (0 : ℝ) < 2 / 3) θ
  have hs := cddPhaseKernel_sq (by norm_num : (0 : ℝ) < 1 / 6) θ
  have hargR : 2 * (2 / 3 : ℝ) * Real.sinh θ / (1 + (2 / 3 : ℝ) ^ (2 : ℕ)) =
      (12 / 13 : ℝ) * Real.sinh θ := by ring
  have hargS : 2 * (1 / 6 : ℝ) * Real.sinh θ / (1 + (1 / 6 : ℝ) ^ (2 : ℕ)) =
      (12 / 37 : ℝ) * Real.sinh θ := by ring
  rw [hargR, show (2 / 3 : ℝ) ^ (2 : ℕ) = 4 / 9 by norm_num] at hr
  rw [hargS, show (1 / 6 : ℝ) ^ (2 : ℕ) = 1 / 36 by norm_num] at hs
  have hr' : cddPhaseKernel (4 / 9) θ = 6 * Real.arctan ((12 / 13 : ℝ) * Real.sinh θ) := by linarith
  have hs' : cddPhaseKernel (1 / 36) θ = 24 * Real.arctan ((12 / 37 : ℝ) * Real.sinh θ) := by linarith
  rw [egbFixedChargeAGibbsFullCollisionCDDPhase_formula, hr', hs']
  ring

/-- The full history gives the coefficients of a convergent odd-spin phase expansion. -/
theorem egbFixedChargeAGibbsFullCollisionCDDPhase_hasSum (n : ℕ) (β t : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ =>
      8 * ((-1 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E *
        Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
        ((2 * m + 1 : ℕ) : ℝ)))
      (egbFixedChargeAGibbsFullCollisionCDDPhase n β E (egbFixedChargeAGibbsCollisionSeriesRapidity t)) := by
  have hc := egbFixedChargeAGibbsCollisionSeriesRapidity_kernel_conditions t
  have hz := hasSum_cddPhaseKernel (by norm_num : (0 : ℝ) ≤ 0)
    (by simp : Real.sqrt (0 : ℝ) * Real.exp |egbFixedChargeAGibbsCollisionSeriesRapidity t| < 1)
  have hr := hasSum_cddPhaseKernel (by norm_num : (0 : ℝ) ≤ 4 / 9) hc.1
  have hs := hasSum_cddPhaseKernel (by norm_num : (0 : ℝ) ≤ 1 / 36) hc.2
  have h := ((hz.mul_left (egbFixedChargeAGibbsDiscardedModeEnergy n β E)).add
    (hr.mul_left (egbFixedChargeAGibbsSlowModeEnergy n β E))).add
    (hs.mul_left (egbFixedChargeAGibbsFastModeEnergy n β E))
  let T (y : ℝ) (m : ℕ) : ℝ := 8 * ((-1 : ℝ) ^ m * y ^ m *
    Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
    ((2 * m + 1 : ℕ) : ℝ))
  change HasSum (fun m : ℕ =>
    egbFixedChargeAGibbsDiscardedModeEnergy n β E * T 0 m +
    egbFixedChargeAGibbsSlowModeEnergy n β E * T (4 / 9) m +
    egbFixedChargeAGibbsFastModeEnergy n β E * T (1 / 36) m)
    (egbFixedChargeAGibbsDiscardedModeEnergy n β E * cddPhaseKernel 0 (egbFixedChargeAGibbsCollisionSeriesRapidity t) +
     egbFixedChargeAGibbsSlowModeEnergy n β E * cddPhaseKernel (4 / 9) (egbFixedChargeAGibbsCollisionSeriesRapidity t) +
     egbFixedChargeAGibbsFastModeEnergy n β E * cddPhaseKernel (1 / 36) (egbFixedChargeAGibbsCollisionSeriesRapidity t)) at h
  have hf : (fun m : ℕ =>
    egbFixedChargeAGibbsDiscardedModeEnergy n β E * T 0 m +
    egbFixedChargeAGibbsSlowModeEnergy n β E * T (4 / 9) m +
    egbFixedChargeAGibbsFastModeEnergy n β E * T (1 / 36) m) =
    (fun m : ℕ => 8 * ((-1 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E *
      Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
      ((2 * m + 1 : ℕ) : ℝ))) := by
    funext m
    dsimp [T]
    rw [egbFixedChargeAGibbsCollisionExcess_full_time_three_rate]
    ring
  have hv : egbFixedChargeAGibbsDiscardedModeEnergy n β E * cddPhaseKernel 0 (egbFixedChargeAGibbsCollisionSeriesRapidity t) +
      egbFixedChargeAGibbsSlowModeEnergy n β E * cddPhaseKernel (4 / 9) (egbFixedChargeAGibbsCollisionSeriesRapidity t) +
      egbFixedChargeAGibbsFastModeEnergy n β E * cddPhaseKernel (1 / 36) (egbFixedChargeAGibbsCollisionSeriesRapidity t) =
      egbFixedChargeAGibbsFullCollisionCDDPhase n β E (egbFixedChargeAGibbsCollisionSeriesRapidity t) := by
    rw [egbFixedChargeAGibbsFullCollisionCDDPhase_formula, cddPhaseKernel_zero]
    ring
  rw [hf, hv] at h
  exact h

end
end GaloisForLFunctions.HTGeometry
