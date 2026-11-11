import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortMollifierKeepsItsLogarithmicScale
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# The low head and coefficient perturbation are negligible

The Weyl head has exponent `791/800<1`. The squared gate coefficient
error contributes two inverse powers of `U`, leaving exponent `−73/200`.
Both fit inside arbitrary slack times `U/log U`.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The entire low-height Weyl head is negligible relative to the gate error scale. -/
theorem eventually_short_detector_head_scale_le {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop,
      C * shortLevinsonCutoff U * (2 * U ^ (53 / 100 : ℝ)) ^ (11 / 8 : ℝ) ≤
        ε * U / Real.log U := by
  have hs := RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le
    (C * (2 : ℝ) ^ (11 / 8 : ℝ)) (9 / 800) (by norm_num) 1 hε
  filter_upwards [hs, eventually_gt_atTop (1 : ℝ)] with U hsi hU
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlog : 0 < Real.log U := Real.log_pos hU
  have hN : (shortLevinsonCutoff U : ℝ) ≤ U ^ (13 / 50 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hU0.le _)
  have he : U ^ (13 / 50 : ℝ) * (2 * U ^ (53 / 100 : ℝ)) ^ (11 / 8 : ℝ) =
      (2 : ℝ) ^ (11 / 8 : ℝ) * (U * U ^ (-(9 / 800 : ℝ))) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hU0.le _),
      ← Real.rpow_mul hU0.le]
    have hp : U ^ (13 / 50 : ℝ) * U ^ ((53 / 100 : ℝ) * (11 / 8)) =
        U * U ^ (-(9 / 800 : ℝ)) := by
      calc
        _ = U ^ ((13 / 50 : ℝ) + (53 / 100) * (11 / 8)) := (Real.rpow_add hU0 _ _).symm
        _ = U ^ (1 + -(9 / 800 : ℝ)) := by norm_num
        _ = _ := by rw [Real.rpow_add hU0, Real.rpow_one]
    calc
      _ = (2 : ℝ) ^ (11 / 8 : ℝ) *
          (U ^ (13 / 50 : ℝ) * U ^ ((53 / 100 : ℝ) * (11 / 8))) := by ring
      _ = _ := by rw [hp]
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ (C * U ^ (13 / 50 : ℝ) * (2 * U ^ (53 / 100 : ℝ)) ^ (11 / 8 : ℝ)) * Real.log U := by
      gcongr
    _ = U * ((C * (2 : ℝ) ^ (11 / 8 : ℝ)) * (U ^ (-(9 / 800 : ℝ)) * Real.log U ^ 1)) := by
      rw [mul_assoc C, he]
      ring
    _ ≤ U * ε := mul_le_mul_of_nonneg_left hsi hU0.le
    _ = _ := mul_comm _ _

/-- The squared coefficient discrepancy is negligible even before division by `U/log U`. -/
theorem eventually_short_detector_coefficient_error_le {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop,
      C * (((13 / 10) / (U - 1)) * Real.exp ((13 / 10) / (U - 1))) ^ 2 *
        shortLevinsonCutoff U * U ^ (11 / 8 : ℝ) ≤ ε * U / Real.log U := by
  let K : ℝ := C * ((13 / 5) * Real.exp 1) ^ 2
  have hs := RHTower.eventually_const_mul_rpow_neg_le K (73 / 200) (by norm_num) hε
  filter_upwards [hs, eventually_ge_atTop (4 : ℝ)] with U hsi hU
  have hU0 : 0 < U := by linarith only [hU]
  have hUm : 0 < U - 1 := by linarith only [hU]
  have hlog : 0 < Real.log U := Real.log_pos (by linarith only [hU])
  have hD0 : 0 ≤ (13 / 10 : ℝ) / (U - 1) := by positivity
  have hD1 : (13 / 10 : ℝ) / (U - 1) ≤ 1 := (div_le_one hUm).mpr (by linarith only [hU])
  have hDU : (13 / 10 : ℝ) / (U - 1) ≤ (13 / 5) / U := by
    apply (div_le_div_iff₀ hUm hU0).mpr
    linarith only [hU]
  have hE : ((13 / 10 : ℝ) / (U - 1)) * Real.exp ((13 / 10) / (U - 1)) ≤
      ((13 / 5) * Real.exp 1) / U := by
    have hh := mul_le_mul hDU (Real.exp_le_exp.mpr hD1) (Real.exp_pos _).le
      (by positivity : (0 : ℝ) ≤ (13 / 5) / U)
    simpa only [div_mul_eq_mul_div] using hh
  have hN : (shortLevinsonCutoff U : ℝ) ≤ U ^ (13 / 50 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hU0.le _)
  have hp : U ^ (13 / 50 : ℝ) * U ^ (11 / 8 : ℝ) / U ^ 2 = U ^ (-(73 / 200 : ℝ)) := by
    rw [show -(73 / 200 : ℝ) = (13 / 50 : ℝ) + 11 / 8 - 2 by norm_num,
      Real.rpow_sub hU0, Real.rpow_add hU0]
    norm_num
  have hbound : C * (((13 / 10 : ℝ) / (U - 1)) * Real.exp ((13 / 10) / (U - 1))) ^ 2 *
      shortLevinsonCutoff U * U ^ (11 / 8 : ℝ) ≤ K * U ^ (-(73 / 200 : ℝ)) := by
    calc
      _ ≤ C * (((13 / 5) * Real.exp 1) / U) ^ 2 * U ^ (13 / 50 : ℝ) * U ^ (11 / 8 : ℝ) := by
        gcongr
      _ = K * (U ^ (13 / 50 : ℝ) * U ^ (11 / 8 : ℝ) / U ^ 2) := by
        dsimp only [K]
        field_simp [hU0.ne']
        ring
      _ = _ := by rw [hp]
  have hlogU : Real.log U ≤ U := by
    have hh := Real.log_le_sub_one_of_pos hU0
    linarith only [hh]
  have hscale : ε ≤ ε * U / Real.log U :=
    (le_div_iff₀ hlog).mpr (mul_le_mul_of_nonneg_left hlogU hε.le)
  exact (hbound.trans hsi).trans hscale

end GaloisForLFunctions.MultiscaleMollifiedZetaField
