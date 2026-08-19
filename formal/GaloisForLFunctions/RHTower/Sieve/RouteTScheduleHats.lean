import GaloisForLFunctions.RHTower.Sieve.RouteTScheduleWorstCase
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# The worst-case data of the schedule

`Sieve/RouteTScheduleWorstCase` needs an upper bound `Ĝ` for the reciprocal-width budget over the
schedule's frequency range `(log z)^{0.6} ≤ log|t| ≤ 2 log z`, and an upper bound `v̂` for the
truncation exponent over the same range.  Both are recorded here together with their polylogarithmic
size, which is what the threshold limits consume.
-/

namespace RHTower.Sieve

noncomputable section

/-- The worst-case reciprocal-width budget on the schedule's frequency range. -/
def routeTBudgetHat (A L : ℝ) : ℝ :=
  10 * routeTZeroFreeDeltaEnvelopeConstant A * (23 + 4 * L) ^ ((9 : ℝ) / 10)
    * (1 + Real.log (23 + 4 * L)) ^ 2

/-- The worst-case truncation exponent on the schedule's frequency range. -/
def routeTTruncHat (L : ℝ) : ℝ :=
  2 / (3 * routeTWidthUpperConst * (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10))

theorem routeTBudgetHat_pos {A L : ℝ} (hL : 1 ≤ L) : 0 < routeTBudgetHat A L := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have h23 : (1 : ℝ) ≤ 23 + 4 * L := by linarith
  have hpow : (0 : ℝ) < (23 + 4 * L) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : (0 : ℝ) ≤ Real.log (23 + 4 * L) := Real.log_nonneg h23
  rw [routeTBudgetHat]
  positivity

/-- **The reciprocal-width budget on the schedule's frequency range.** -/
theorem routeTReciprocalBudget_le_hat {A t L : ℝ} (ht : 1 ≤ |t|) (hL : Real.log |t| ≤ 2 * L) :
    routeTReciprocalBudget A t ≤ routeTBudgetHat A L := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have h1 : (1 : ℝ) ≤ routeTHeightBudget t := one_le_routeTHeightBudget ht
  have h2 : routeTHeightBudget t ≤ 23 + 4 * L := by
    rw [routeTHeightBudget]; linarith
  have hshape := surrogate_shape_mono h1 h2
  rw [routeTReciprocalBudget, routeTBudgetHat]
  nlinarith [hshape, hD]

/-- **The truncation exponent on the schedule's frequency range.** -/
theorem routeTTruncExponent_le_hat {t L : ℝ} (hL : 1 ≤ L) (ht : L ^ (0.6 : ℝ) ≤ Real.log |t|) :
    routeTTruncExponent t ≤ routeTTruncHat L := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK := routeTWidthUpperConst_pos
  have hLp : (0 : ℝ) < L ^ (0.6 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (0 : ℝ) < Real.log |t| := lt_of_lt_of_le hLp ht
  have hdiv : L ^ (0.6 : ℝ) / Real.log 2 ≤ Real.log |t| / Real.log 2 :=
    div_le_div_of_nonneg_right ht hlog2.le
  have hpow : (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10)
      ≤ (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
  have hp0 : (0 : ℝ) < (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [routeTTruncExponent, routeTTruncHat]
  have hval : 2 * (1 / (routeTWidthUpperConst
        * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3
      = 2 / (3 * routeTWidthUpperConst * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10)) := by
    field_simp
  rw [hval]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  have hc : (0 : ℝ) ≤ 3 * routeTWidthUpperConst := by linarith
  nlinarith [hpow, hK]

/-- **The worst-case budget is a power times a polylogarithm.** -/
theorem routeTBudgetHat_le_polylog {A L : ℝ} (hL : 1 ≤ L) :
    routeTBudgetHat A L
      ≤ 211680 * routeTZeroFreeDeltaEnvelopeConstant A * L ^ (0.9 : ℝ)
          * (1 + |Real.log L|) ^ 2 := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  have hle : (23 : ℝ) + 4 * L ≤ 27 * L := by linarith
  have h27 : Real.log 27 ≤ 27 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 27 by norm_num)
    linarith
  -- the power
  have hpow : (23 + 4 * L) ^ ((9 : ℝ) / 10) ≤ 27 * L ^ (0.9 : ℝ) := by
    have h1 : (23 + 4 * L) ^ ((9 : ℝ) / 10) ≤ (27 * L) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow (by linarith) hle (by norm_num)
    have h2 : (27 * L) ^ ((9 : ℝ) / 10) = (27 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) :=
      Real.mul_rpow (by norm_num) hL0.le
    have h3 : (27 : ℝ) ^ ((9 : ℝ) / 10) ≤ (27 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h3
    have h4 : L ^ ((9 : ℝ) / 10) = L ^ (0.9 : ℝ) := by norm_num
    have hLp : (0 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
    rw [h2, h4] at h1
    nlinarith [h1, h3, hLp]
  -- the logarithm
  have hlogsq : (1 + Real.log (23 + 4 * L)) ^ 2 ≤ 784 * (1 + Real.log L) ^ 2 := by
    have h1 : Real.log (23 + 4 * L) ≤ Real.log 27 + Real.log L := by
      have hstep : Real.log (23 + 4 * L) ≤ Real.log (27 * L) :=
        Real.log_le_log (by linarith) hle
      rwa [Real.log_mul (by norm_num) (ne_of_gt hL0)] at hstep
    have h2 : (1 : ℝ) + Real.log (23 + 4 * L) ≤ 28 * (1 + Real.log L) := by linarith
    have h3 : (0 : ℝ) ≤ 1 + Real.log (23 + 4 * L) := by
      have : (0 : ℝ) ≤ Real.log (23 + 4 * L) := Real.log_nonneg (by linarith)
      linarith
    nlinarith [h2, h3]
  rw [routeTBudgetHat, habs]
  have hs0 : (0 : ℝ) ≤ (1 + Real.log (23 + 4 * L)) ^ 2 := sq_nonneg _
  have hLp : (0 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
  have hXY : (23 + 4 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (23 + 4 * L)) ^ 2
      ≤ (27 * L ^ (0.9 : ℝ)) * (784 * (1 + Real.log L) ^ 2) :=
    mul_le_mul hpow hlogsq hs0 (by positivity)
  have hL2 : 10 * routeTZeroFreeDeltaEnvelopeConstant A * (23 + 4 * L) ^ ((9 : ℝ) / 10)
      * (1 + Real.log (23 + 4 * L)) ^ 2
      = (10 * routeTZeroFreeDeltaEnvelopeConstant A) * ((23 + 4 * L) ^ ((9 : ℝ) / 10)
          * (1 + Real.log (23 + 4 * L)) ^ 2) := by ring
  have hR2 : 211680 * routeTZeroFreeDeltaEnvelopeConstant A * L ^ (0.9 : ℝ)
      * (1 + Real.log L) ^ 2
      = (10 * routeTZeroFreeDeltaEnvelopeConstant A)
          * ((27 * L ^ (0.9 : ℝ)) * (784 * (1 + Real.log L) ^ 2)) := by ring
  rw [hL2, hR2]
  exact mul_le_mul_of_nonneg_left hXY (by linarith [hD])

/-- **The worst-case truncation exponent is a negative power.** -/
theorem routeTTruncHat_le {L : ℝ} (hL : 1 ≤ L) :
    routeTTruncHat L ≤ 2 / (3 * routeTWidthUpperConst) * L ^ (-(0.54 : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hK := routeTWidthUpperConst_pos
  have hL0 : (0 : ℝ) < L := by linarith
  have hLp : (0 : ℝ) < L ^ (0.6 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hdiv : L ^ (0.54 : ℝ) ≤ (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10) := by
    have hge : L ^ (0.6 : ℝ) ≤ L ^ (0.6 : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      nlinarith [hLp, hlog2le]
    have hmono : (L ^ (0.6 : ℝ)) ^ ((9 : ℝ) / 10)
        ≤ (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow hLp.le hge (by norm_num)
    have hval : (L ^ (0.6 : ℝ)) ^ ((9 : ℝ) / 10) = L ^ (0.54 : ℝ) := by
      rw [← Real.rpow_mul hL0.le]
      norm_num
    rwa [hval] at hmono
  have hp0 : (0 : ℝ) < L ^ (0.54 : ℝ) := Real.rpow_pos_of_pos hL0 _
  rw [routeTTruncHat]
  have hstep : 2 / (3 * routeTWidthUpperConst * (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10))
      ≤ 2 / (3 * routeTWidthUpperConst * L ^ (0.54 : ℝ)) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith [hdiv, hK]
  refine hstep.trans (le_of_eq ?_)
  rw [Real.rpow_neg hL0.le]
  field_simp

end

end RHTower.Sieve
