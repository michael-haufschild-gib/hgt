import GaloisForLFunctions.HTGeometry.WalshPowerWeights
import GaloisForLFunctions.RHTower.PaperWoldNearEnvelope

/-! # Native Wold envelopes in the Walsh three-quarter domain

The existing logarithmic increment estimate supplies every hypothesis of the
separated power-kernel construction, including at the old half-power boundary.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

abbrev PaperWoldWalshBand := {t : ℝ // 1 / 2 ≤ t ∧ t < 3 / 4}

def paperWoldWalshEnvelopeParameters (t : PaperWoldWalshBand) : PaperWoldNearParameters where
  t := t.val + 1 / 4
  eta := 0
  t_nonneg := by linarith [t.property.1]
  eta_nonneg := le_rfl
  budget := by linarith [t.property.2]

theorem paperWoldWalshEnvelope_slack (t : PaperWoldWalshBand) :
    paperWoldSlack (paperWoldWalshEnvelopeParameters t) = (3 / 4 - t.val) / 2 := by
  unfold paperWoldSlack paperWoldWalshEnvelopeParameters
  ring

/-- Every envelope field is proved from the actual source coefficients. -/
def paperWoldWalshPowerData (t : PaperWoldWalshBand) : WalshPowerKernel where
  row n := (((n : ℝ) + 1) ^ (2 * t.val) * xiHeatCassiniWoldNatIncrement n : ℝ)
  column n := (xiHeatCassiniWoldNatIncrement n : ℝ)
  alpha := 2 * t.val + paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1
  beta := paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1
  bound := paperWoldEnvelopeConstant (paperWoldWalshEnvelopeParameters t)
  alpha_nonneg := by
    linarith [t.property.1, (paperWoldSlack_bounds (paperWoldWalshEnvelopeParameters t)).1]
  sum_lt := by
    rw [paperWoldWalshEnvelope_slack]
    linarith [t.property.2]
  bound_nonneg := (paperWoldEnvelopeConstant_pos _).le
  row_bound n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have h := mul_le_mul_of_nonneg_left
      (paperWold_increment_power_bound (paperWoldWalshEnvelopeParameters t) n)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (2 * t.val))
    have he : 2 * t.val + paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1 =
        2 * t.val + (paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1) := by ring
    rw [he, Real.rpow_add (by positivity)]
    simpa only [mul_left_comm] using h
  column_bound n := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact paperWold_increment_power_bound (paperWoldWalshEnvelopeParameters t) n

theorem paperWoldWalshPowerData_budget (t : PaperWoldWalshBand) :
    (paperWoldWalshPowerData t).alpha + (paperWoldWalshPowerData t).beta + 1 / 2 = t.val - 3 / 4 := by
  change (2 * t.val + paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1) +
    (paperWoldSlack (paperWoldWalshEnvelopeParameters t) - 1) + 1 / 2 = _
  rw [paperWoldWalshEnvelope_slack]
  ring

end
end RHTower
