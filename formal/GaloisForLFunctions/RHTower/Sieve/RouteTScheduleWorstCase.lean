import GaloisForLFunctions.RHTower.Sieve.RouteTScheduleRegimes

/-!
# The three thresholds at their worst case

Each threshold of `Sieve/RouteTScheduleRegimes` is monotone in the block top `log i` and in the
frequency `log|t|`, so on the schedule's ranges it suffices to check it once, at the extreme values.
The reductions here are pure monotonicity: the prefactor is evaluated at the largest admissible
data, the saving at the smallest.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The contour threshold at its worst case.** -/
theorem contour_threshold_worst {C Li Lz Lt G Ghat delta : ℝ}
    (hC : 0 < C) (hLz : 0 ≤ Lz) (hG0 : 0 < G) (hGhat : G ≤ Ghat) (hdelta : 0 < delta)
    (hLt0 : 0 ≤ Lt) (hLt : Lt ≤ 2 * Lz) (hLi : Li ≤ Lz) (hLimin : Lz ^ (0.99 : ℝ) ≤ Li)
    (hkey : Real.log (9 * C * (1 + (4 + 2 * Lz) * Ghat + 2 * Lz) * (9 * (2 + Lz)))
        ≤ min delta (1 / Ghat) / 6 * Lz ^ (0.99 : ℝ)) :
    Real.log (9 * C * (1 + (4 + Lt) * G + 2 * Li) * (9 * (2 + Lz)))
      ≤ min delta (1 / G) / 6 * Li := by
  have hGhat0 : (0 : ℝ) < Ghat := lt_of_lt_of_le hG0 hGhat
  have hinv : 1 / Ghat ≤ 1 / G := one_div_le_one_div_of_le hG0 hGhat
  have hmin : min delta (1 / Ghat) ≤ min delta (1 / G) := le_min (min_le_left _ _)
    (le_trans (min_le_right _ _) hinv)
  have hmin0 : (0 : ℝ) ≤ min delta (1 / Ghat) := le_min hdelta.le (by positivity)
  have hLipos : (0 : ℝ) ≤ Lz ^ (0.99 : ℝ) := Real.rpow_nonneg hLz _
  have hsav : min delta (1 / Ghat) / 6 * Lz ^ (0.99 : ℝ) ≤ min delta (1 / G) / 6 * Li := by
    have h1 : min delta (1 / Ghat) / 6 * Lz ^ (0.99 : ℝ)
        ≤ min delta (1 / G) / 6 * Lz ^ (0.99 : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hLipos
      linarith
    have h2 : min delta (1 / G) / 6 * Lz ^ (0.99 : ℝ) ≤ min delta (1 / G) / 6 * Li := by
      refine mul_le_mul_of_nonneg_left hLimin ?_
      have : (0 : ℝ) ≤ min delta (1 / G) := le_trans hmin0 hmin
      linarith
    linarith
  refine le_trans (Real.log_le_log ?_ ?_) (le_trans hkey hsav)
  · have h1 : (0 : ℝ) ≤ (4 + Lt) * G := by positivity
    have h2 : (0 : ℝ) ≤ Li := le_trans hLipos hLimin
    have h3 : (0 : ℝ) < 9 * C * (1 + (4 + Lt) * G + 2 * Li) := by positivity
    have h4 : (0 : ℝ) < 9 * (2 + Lz) := by linarith
    positivity
  · have hGt : (4 + Lt) * G ≤ (4 + 2 * Lz) * Ghat := by
      have hfac : (4 : ℝ) + Lt ≤ 4 + 2 * Lz := by linarith
      exact mul_le_mul hfac hGhat hG0.le (by linarith)
    have hprod : 9 * C * (1 + (4 + Lt) * G + 2 * Li)
        ≤ 9 * C * (1 + (4 + 2 * Lz) * Ghat + 2 * Lz) := by
      have : (1 : ℝ) + (4 + Lt) * G + 2 * Li ≤ 1 + (4 + 2 * Lz) * Ghat + 2 * Lz := by linarith
      nlinarith [this, hC]
    have hpos : (0 : ℝ) < 9 * (2 + Lz) := by linarith
    exact mul_le_mul_of_nonneg_right hprod hpos.le

/-- **The truncation threshold at its worst case.** -/
theorem trunc_threshold_worst {C Li Lz Lt G Ghat v vhat : ℝ}
    (hC : 0 < C) (hLz : 0 ≤ Lz) (hG0 : 0 < G) (hGhat : G ≤ Ghat)
    (hv0 : 0 ≤ v) (hvhat : v ≤ vhat) (hLt0 : 0 ≤ Lt) (hLt : Lt ≤ 2 * Lz)
    (hLtmin : Lz ^ (0.6 : ℝ) ≤ Lt) (hLi0 : 0 ≤ Li) (hLi : Li ≤ Lz)
    (hkey : vhat * Lz
        + Real.log (9 * C * (3 : ℝ) ^ vhat * (2 + Lz ^ 2 + (4 + 2 * Lz) * Ghat)
            * (9 * (2 + Lz))) ≤ Lz ^ (0.6 : ℝ)) :
    v * Li + Real.log (9 * C * (3 : ℝ) ^ v * (2 + Li ^ 2 + (4 + Lt) * G) * (9 * (2 + Lz)))
      ≤ Lt := by
  have hGhat0 : (0 : ℝ) < Ghat := lt_of_lt_of_le hG0 hGhat
  have hvLi : v * Li ≤ vhat * Lz := by
    have h1 : v * Li ≤ v * Lz := mul_le_mul_of_nonneg_left hLi hv0
    have h2 : v * Lz ≤ vhat * Lz := mul_le_mul_of_nonneg_right hvhat hLz
    linarith
  have h3v : (3 : ℝ) ^ v ≤ (3 : ℝ) ^ vhat :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hvhat
  have h3v0 : (0 : ℝ) < (3 : ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) _
  have hQ : (2 : ℝ) + Li ^ 2 + (4 + Lt) * G ≤ 2 + Lz ^ 2 + (4 + 2 * Lz) * Ghat := by
    have hsq : Li ^ 2 ≤ Lz ^ 2 := by nlinarith [hLi0, hLi]
    have hfac : (4 : ℝ) + Lt ≤ 4 + 2 * Lz := by linarith
    have hGt : (4 + Lt) * G ≤ (4 + 2 * Lz) * Ghat :=
      mul_le_mul hfac hGhat hG0.le (by linarith)
    linarith
  have hQ0 : (0 : ℝ) < 2 + Li ^ 2 + (4 + Lt) * G := by positivity
  have hprod : 9 * C * (3 : ℝ) ^ v * (2 + Li ^ 2 + (4 + Lt) * G)
      ≤ 9 * C * (3 : ℝ) ^ vhat * (2 + Lz ^ 2 + (4 + 2 * Lz) * Ghat) := by
    have h1 : 9 * C * (3 : ℝ) ^ v ≤ 9 * C * (3 : ℝ) ^ vhat := by nlinarith [h3v, hC]
    have h2 : (0 : ℝ) < 9 * C * (3 : ℝ) ^ v := by positivity
    exact mul_le_mul h1 hQ hQ0.le (by nlinarith [h2, h3v])
  have hlogle : Real.log (9 * C * (3 : ℝ) ^ v * (2 + Li ^ 2 + (4 + Lt) * G) * (9 * (2 + Lz)))
      ≤ Real.log (9 * C * (3 : ℝ) ^ vhat * (2 + Lz ^ 2 + (4 + 2 * Lz) * Ghat)
          * (9 * (2 + Lz))) := by
    refine Real.log_le_log (by positivity) ?_
    exact mul_le_mul_of_nonneg_right hprod (by linarith)
  linarith [hvLi, hlogle, hkey, hLtmin]

end

end RHTower.Sieve
