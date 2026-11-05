import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightHalfGaussBounds
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits

/-!
# Source envelopes in the saddle slope

When `1 + log(4T) ≤ 8α`, the typical-height logarithmic derivative is
bounded by an affine function of `log α`. The logarithm of its lower-tail
source ratio has the same form. These envelopes separate the source
estimates from the choice of heat time.
-/

open Filter Topology
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- An affine logarithmic envelope for the source slope error. -/
def typicalSlopeEnvelope (η α : ℝ) : ℝ :=
  (96 / η ^ 2) * Real.log α + (96 * Real.log 8 + 216) / η ^ 2 + 4

/-- An affine logarithmic envelope for the logarithm of the source ratio. -/
def typicalTailLogEnvelope (η α : ℝ) : ℝ :=
  Real.log 9 + (4 + 48 / η) * Real.log (8 * α) + 108 / η + 3

theorem typicalSlopeEnvelope_nonneg {η α : ℝ} (hα : 1 ≤ α) :
    0 ≤ typicalSlopeEnvelope η α := by
  unfold typicalSlopeEnvelope
  have hlog := Real.log_nonneg hα
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  positivity

/-- The dyadic source slope is controlled by the saddle scale alone. -/
theorem typicalXiSlopeError_le_envelope {η T α : ℝ}
    (hη : 0 < η) (hT : 8 ≤ T) (hα : 1 ≤ α)
    (hscale : 1 + Real.log (4 * T) ≤ 8 * α) :
    typicalXiSlopeError η T ≤ typicalSlopeEnvelope η α := by
  have hT0 : 0 < T := by linarith only [hT]
  have hL : 0 < 1 + Real.log (4 * T) := by
    have := Real.log_nonneg (show 1 ≤ 4 * T by linarith only [hT])
    linarith only [this]
  have hα0 : 0 < α := by linarith only [hα]
  have hlog := Real.log_le_log hL hscale
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hα0.ne'] at hlog
  unfold typicalXiSlopeError typicalSlopeEnvelope
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 96 / η ^ 2 by positivity)
  nlinarith only [hm]

/-- The lower-tail source ratio has a logarithmic exponential envelope. -/
theorem typicalXiTailFactor_le_envelope {η T α : ℝ}
    (hη : 0 < η) (hT : 8 ≤ T) (hα : 1 ≤ α)
    (hscale : 1 + Real.log (4 * T) ≤ 8 * α) :
    typicalXiTailFactor η T ≤ Real.exp (typicalTailLogEnvelope η α) := by
  have hL : 0 < 1 + Real.log (4 * T) := by
    have := Real.log_nonneg (show 1 ≤ 4 * T by linarith only [hT])
    linarith only [this]
  have hα8 : 1 ≤ 8 * α := by linarith only [hα]
  have hpow := pow_le_pow_left₀ hL.le hscale 4
  have hone : (1 : ℝ) ≤ (8 * α) ^ (4 : ℕ) := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hα8 4
  have hpre : 3 * ((1 + Real.log (4 * T)) ^ (4 : ℕ) + 2) ≤
      9 * (8 * α) ^ (4 : ℕ) := by linarith only [hpow, hone]
  have hlog := Real.log_le_log hL hscale
  have hexp : 12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η + 3 ≤
      12 * (4 * Real.log (8 * α) + 9) / η + 3 := by
    gcongr
  have hpowexp : (8 * α) ^ (4 : ℕ) = Real.exp (4 * Real.log (8 * α)) := by
    have hlogpow := Real.log_pow (8 * α) 4
    norm_num only [Nat.cast_ofNat] at hlogpow
    rw [← hlogpow, Real.exp_log (by positivity)]
  have hpreexp : Real.exp (Real.log 9 + 4 * Real.log (8 * α)) =
      9 * (8 * α) ^ (4 : ℕ) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), ← hpowexp]
  unfold typicalXiTailFactor
  calc
    _ ≤ 9 * (8 * α) ^ (4 : ℕ) *
        Real.exp (12 * (4 * Real.log (8 * α) + 9) / η + 3) := by
      exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ = Real.exp (typicalTailLogEnvelope η α) := by
      rw [← hpreexp, ← Real.exp_add]
      congr 1
      unfold typicalTailLogEnvelope
      ring

/-- A logarithmic source slope is negligible across a Gaussian of width `α⁻¹/²`. -/
theorem tendsto_affineLog_div_sqrt (A D : ℝ) :
    Tendsto (fun α : ℝ => (A * Real.log α + D) / Real.sqrt α) atTop (𝓝 0) := by
  have hl : Tendsto (fun α : ℝ => Real.log α / Real.sqrt α) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using _root_.RHTower.Sieve.tendsto_rpow_log_div_sqrt 1
  have hc : Tendsto (fun α : ℝ => D / Real.sqrt α) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hh : Tendsto (fun α : ℝ => A * (Real.log α / Real.sqrt α) + D / Real.sqrt α)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hl.const_mul A).add hc
  convert hh using 1
  ext α
  ring

/-- Affine logarithmic losses are sublinear. -/
theorem tendsto_affineLog_div_self (A D : ℝ) :
    Tendsto (fun α : ℝ => (A * Real.log α + D) / α) atTop (𝓝 0) := by
  have hh := (tendsto_affineLog_div_sqrt A D).div_atTop Real.tendsto_sqrt_atTop
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
  rw [div_div, ← pow_two, Real.sq_sqrt hα.le]

/-- Every positive linear rate eventually absorbs an affine logarithmic loss. -/
theorem eventually_affineLog_le_linear (A D : ℝ) {k : ℝ} (hk : 0 < k) :
    ∀ᶠ α : ℝ in atTop, A * Real.log α + D ≤ k * α := by
  have hh := (tendsto_affineLog_div_self A D).eventually (eventually_le_nhds hk)
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with α ha hα
  exact (div_le_iff₀ hα).mp ha

/-- The Gaussian-scale slope error tends to zero. -/
theorem tendsto_typicalSlopeEnvelope_div_sqrt (η : ℝ) :
    Tendsto (fun α : ℝ => typicalSlopeEnvelope η α / Real.sqrt α) atTop (𝓝 0) := by
  have hh := tendsto_affineLog_div_sqrt (96 / η ^ 2)
    ((96 * Real.log 8 + 216) / η ^ 2 + 4)
  convert hh using 1
  ext α
  unfold typicalSlopeEnvelope
  ring

/-- The source-ratio envelope is smaller than any positive linear exponential rate. -/
theorem eventually_typicalTailLogEnvelope_le {η k : ℝ} (hk : 0 < k) :
    ∀ᶠ α : ℝ in atTop, typicalTailLogEnvelope η α ≤ k * α := by
  have hh := eventually_affineLog_le_linear (4 + 48 / η)
    (Real.log 9 + (4 + 48 / η) * Real.log 8 + 108 / η + 3) hk
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with α ha hα
  unfold typicalTailLogEnvelope
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hα.ne']
  linarith only [ha]

#print axioms typicalXiTailFactor_le_envelope
#print axioms tendsto_typicalSlopeEnvelope_div_sqrt

end

end GaloisForLFunctions.ZeroConfigurationGeometry
