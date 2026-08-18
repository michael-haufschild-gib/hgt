import GaloisForLFunctions.RHTower.Sieve.ScaledEnvelopeEstimate

/-!
# The Route-T width and the height cost are monotone in the frequency

The annulus estimate needs a bound valid uniformly over a range of frequencies, so the width's
polylogarithmic surrogate and the height cost it produces have to be compared across that range.
Both comparisons are immediate from the explicit shape `2 log(t+2) + 1` of the height envelope.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- **The width's polylogarithmic surrogate is antitone in the frequency.** -/
theorem routeTWidthPolylogLower_antitone {A τ σ : ℝ} (h : |τ| ≤ |σ|) :
    routeTWidthPolylogLower A σ ≤ routeTWidthPolylogLower A τ := by
  have hτ0 : (0 : ℝ) ≤ |τ| := abs_nonneg τ
  have hσ0 : (0 : ℝ) ≤ |σ| := abs_nonneg σ
  set Zτ : ℝ := routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) with hZτ
  set Zσ : ℝ := routeTLogHeightEnvelope (4 * (3 * |σ| / 2 + 1)) with hZσ
  have hZτ1 : (1 : ℝ) ≤ Zτ := routeTLogHeightEnvelope_one_le (by linarith)
  have hZσ1 : (1 : ℝ) ≤ Zσ := routeTLogHeightEnvelope_one_le (by linarith)
  have hZ : Zτ ≤ Zσ := by
    rw [hZτ, hZσ, routeTLogHeightEnvelope, routeTLogHeightEnvelope]
    have : (4 : ℝ) * (3 * |τ| / 2 + 1) + 2 ≤ 4 * (3 * |σ| / 2 + 1) + 2 := by linarith
    have hlog := Real.log_le_log (by linarith) this
    linarith
  have hpow : Zτ ^ ((9 : ℝ) / 10) ≤ Zσ ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow (by linarith) hZ (by norm_num)
  have hlogZτ : (0 : ℝ) ≤ Real.log Zτ := Real.log_nonneg hZτ1
  have hlogZ : Real.log Zτ ≤ Real.log Zσ := Real.log_le_log (by linarith) hZ
  have hsq : (1 + Real.log Zτ) ^ 2 ≤ (1 + Real.log Zσ) ^ 2 := by
    refine pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hden1 : (0 : ℝ) < 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zτ ^ ((9 : ℝ) / 10)
      * (1 + Real.log Zτ) ^ 2 := by
    have h1 : (0 : ℝ) < Zτ ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0 : ℝ) < (1 + Real.log Zτ) ^ 2 := by positivity
    positivity
  have hpow0 : (0 : ℝ) ≤ Zτ ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Zτ) ^ 2 := sq_nonneg _
  have hden : 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zτ ^ ((9 : ℝ) / 10)
        * (1 + Real.log Zτ) ^ 2
      ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zσ ^ ((9 : ℝ) / 10)
        * (1 + Real.log Zσ) ^ 2 := by
    have hstep : 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zτ ^ ((9 : ℝ) / 10)
        ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zσ ^ ((9 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h0 : (0 : ℝ) ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * Zσ ^ ((9 : ℝ) / 10) := by
      have : (0 : ℝ) ≤ Zσ ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
      positivity
    exact mul_le_mul hstep hsq hsq0 h0
  rw [routeTWidthPolylogLower, routeTWidthPolylogLower, ← hZτ, ← hZσ]
  exact one_div_le_one_div_of_le hden1 hden

/-- **The height cost, bounded uniformly over a frequency range.** -/
theorem scaledHeightMajorant_le_of_le {A τ σ t₀ : ℝ} (ht0 : 0 < t₀) (hlo : t₀ ≤ |τ|)
    (hhi : |τ| ≤ |σ|) (hτ1 : 1 ≤ |τ|) :
    scaledHeightMajorant A τ
      ≤ 1 / t₀ + Real.log (3 * |σ| / 2) / routeTWidthPolylogLower A σ := by
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hplwτ := routeTWidthPolylogLower_pos A τ
  have hplwσ := routeTWidthPolylogLower_pos A σ
  have hanti := routeTWidthPolylogLower_antitone (A := A) (τ := τ) (σ := σ) hhi
  have hlogτ : (0 : ℝ) ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
  have hlogσ : Real.log (3 * |τ| / 2) ≤ Real.log (3 * |σ| / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hinv : 1 / routeTWidthPolylogLower A τ ≤ 1 / routeTWidthPolylogLower A σ :=
    one_div_le_one_div_of_le hplwσ hanti
  have hfirst : 1 / |τ| ≤ 1 / t₀ := one_div_le_one_div_of_le ht0 hlo
  have hsecond : Real.log (3 * |τ| / 2) / routeTWidthPolylogLower A τ
      ≤ Real.log (3 * |σ| / 2) / routeTWidthPolylogLower A σ :=
    div_le_div₀ (le_trans hlogτ hlogσ) hlogσ hplwσ hanti
  rw [scaledHeightMajorant]
  linarith

end

end RHTower.Sieve
