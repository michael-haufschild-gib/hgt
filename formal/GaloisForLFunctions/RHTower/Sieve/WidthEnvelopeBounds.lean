import GaloisForLFunctions.RHTower.Sieve.RouteTWidthAntitone

/-!
# Explicit bounds for the Route-T width surrogate

`routeTLogHeightEnvelope t = 2 log(t+2) + 1` is elementary, so the width surrogate and its
reciprocal are elementary functions of the height.
-/

namespace RHTower.Sieve

open Real

noncomputable section

theorem inv_routeTWidthPolylogLower_eq (A τ : ℝ) :
    1 / routeTWidthPolylogLower A τ
      = 10 * routeTZeroFreeDeltaEnvelopeConstant A
        * (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10)
        * (1 + Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)))) ^ 2 := by
  rw [routeTWidthPolylogLower, one_div_one_div]

/-- The height envelope of a frequency, bounded by the logarithm of the frequency. -/
theorem routeTLogHeightEnvelope_le {τ : ℝ} (hτ : 1 ≤ |τ|) :
    routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) ≤ 10 + 2 * Real.log |τ| := by
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hle : 4 * (3 * |τ| / 2 + 1) + 2 ≤ 12 * |τ| := by linarith
  have hlog : Real.log (4 * (3 * |τ| / 2 + 1) + 2) ≤ Real.log (12 * |τ|) :=
    Real.log_le_log (by linarith) hle
  have hsplit : Real.log (12 * |τ|) = Real.log 12 + Real.log |τ| :=
    Real.log_mul (by norm_num) (ne_of_gt hτ0)
  have hl12 : Real.log 12 ≤ 4 := by
    have h16 : Real.log 12 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    linarith
  rw [routeTLogHeightEnvelope]
  linarith [hlog, hsplit, hl12]

/-- The reciprocal width surrogate, bounded above. -/
theorem inv_routeTWidthPolylogLower_le {A τ Z : ℝ} (hτ : 1 ≤ |τ|)
    (hZ : routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) ≤ Z) (hZ1 : 1 ≤ Z) :
    1 / routeTWidthPolylogLower A τ
      ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2 := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hE1 : (1 : ℝ) ≤ routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by
    refine routeTLogHeightEnvelope_one_le ?_
    have := abs_nonneg τ
    linarith
  have hE0 : (0 : ℝ) < routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by linarith
  have hpow : (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10)
      ≤ Z ^ ((9 : ℝ) / 10) := Real.rpow_le_rpow (by linarith) hZ (by norm_num)
  have hlog : Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ≤ Real.log Z :=
    Real.log_le_log hE0 hZ
  have hlog0 : (0 : ℝ) ≤ Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) :=
    Real.log_nonneg hE1
  have hsq : (1 + Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)))) ^ 2
      ≤ (1 + Real.log Z) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [inv_routeTWidthPolylogLower_eq]
  have hpow0 : (0 : ℝ) ≤ (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10) :=
    Real.rpow_nonneg hE0.le _
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)))) ^ 2 :=
    sq_nonneg _
  have hstep : 10 * routeTZeroFreeDeltaEnvelopeConstant A
        * (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10)
      ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hZpow0 : (0 : ℝ) ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10) := by
    have : (0 : ℝ) ≤ Z ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
    positivity
  exact mul_le_mul hstep hsq hsq0 hZpow0

/-- The width surrogate, bounded below. -/
theorem routeTWidthPolylogLower_ge {A τ Z : ℝ} (hτ : 1 ≤ |τ|)
    (hZ : routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) ≤ Z) (hZ1 : 1 ≤ Z) :
    1 / (10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2)
      ≤ routeTWidthPolylogLower A τ := by
  have hplw := routeTWidthPolylogLower_pos A τ
  have hle := inv_routeTWidthPolylogLower_le (A := A) hτ hZ hZ1
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ0 : (0 : ℝ) < Z ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hlogZ : (0 : ℝ) ≤ Real.log Z := Real.log_nonneg hZ1
  have hden : (0 : ℝ) < 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
      * (1 + Real.log Z) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  rw [div_le_iff₀ hplw] at hle
  nlinarith [hle, hplw, hden]

end

end RHTower.Sieve
