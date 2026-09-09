import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitPath
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsZeros
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsMaximum

/-!
# Exact finite-state meaning of the mean energy deficit

The deficit is the error made by using the arithmetic mean energy as the
barrier. It is nonnegative, strictly smaller than the actual barrier,
and vanishes exactly when the mean is the intermediate equilibrium.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanGibbsDeficit_gap_difference (w φ τ l : ℝ) :
    egbFixedChargeAMeanGibbsDeficit w φ τ l = egbFixedChargeAGibbsBarrier w φ τ l -
      egbFixedChargeAInteriorGibbsGap w φ τ l 0 := by
  unfold egbFixedChargeAMeanGibbsDeficit egbFixedChargeAGibbsBarrier egbFixedChargeAInteriorGibbsGap
  rw [egbFixedChargeAInteriorRadius_mean]
  ring

theorem egbFixedChargeAMeanGibbsDeficit_bounds (w φ τ l : ℝ) :
    0 ≤ egbFixedChargeAMeanGibbsDeficit w φ τ l ∧
      egbFixedChargeAMeanGibbsDeficit w φ τ l < egbFixedChargeAGibbsBarrier w φ τ l := by
  have hb := egbFixedChargeAInteriorGibbsGap_bounds w φ τ l 0
  have hp : 0 < egbFixedChargeAInteriorGibbsGap w φ τ l 0 :=
    (egbFixedChargeAInteriorGibbsGap_pos_iff w φ τ l 0).mpr (by simp only [cos_zero, ne_eq, one_ne_zero, not_false_eq_true])
  rw [egbFixedChargeAMeanGibbsDeficit_gap_difference]
  constructor <;> linarith [hb.2]

theorem egbFixedChargeAMeanGibbsDeficit_zero_iff (w φ τ l : ℝ) :
    egbFixedChargeAMeanGibbsDeficit w φ τ l = 0 ↔ egbFixedChargeAMiddleRadius w φ τ = egbFixedChargeAMeanRadius w φ τ := by
  rw [egbFixedChargeAMeanGibbsDeficit_gap_difference, sub_eq_zero, eq_comm,
    egbFixedChargeAInteriorGibbsGap_maximizer_iff, sin_zero]
  have h := egbFixedChargeAInteriorRadius_middle_iff w φ τ 0
  rw [egbFixedChargeAInteriorRadius_mean, sin_zero] at h
  exact h.symm.trans eq_comm

theorem egbFixedChargeAMeanGibbsDeficit_ratio_bounds (w φ τ l : ℝ) :
    0 ≤ egbFixedChargeAMeanGibbsDeficit w φ τ l / egbFixedChargeAGibbsBarrier w φ τ l ∧
      egbFixedChargeAMeanGibbsDeficit w φ τ l / egbFixedChargeAGibbsBarrier w φ τ l < 1 := by
  have hb := egbFixedChargeAMeanGibbsDeficit_bounds w φ τ l
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  constructor
  · exact div_nonneg hb.1 hB.le
  · apply (div_lt_iff₀ hB).2
    simpa only [one_mul] using hb.2

end GaloisForLFunctions.HTGeometry
