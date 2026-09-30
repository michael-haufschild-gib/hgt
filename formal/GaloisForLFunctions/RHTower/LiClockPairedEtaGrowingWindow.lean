import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Decay of the paired-eta source error on growing clock windows

The exact source quotient envelope is
`(6400 + 48 * log (2N+1)) * (2N+1)^(-1/4)`. It is nonnegative and tends to
zero; the separate value-tail envelope eventually meets the finite
denominator threshold `1 / 16`.

Multiplication by the growing-window factor `exp (c * log (2N+1) / r)`
leaves the negative power `-(1/4-c/r)`. For `0 < c < r/4` this still tends
to zero. The sharper hyperbolic-sine envelope tends to zero as well.
These are error-envelope limits and do not assert clock positivity.
-/

open Filter Topology

namespace RHTower
noncomputable section

/-- The exact calibrated paired-eta quotient error envelope. -/
def liClockPairedEtaSourceErrorEnvelope (N : ℕ) : ℝ :=
  (6400 + 48 * Real.log (2 * (N : ℝ) + 1)) *
    (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ))

theorem liClockPairedEtaSourceErrorEnvelope_nonneg (N : ℕ) :
    0 ≤ liClockPairedEtaSourceErrorEnvelope N := by
  have hlog : 0 ≤ Real.log (2 * (N : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  unfold liClockPairedEtaSourceErrorEnvelope
  positivity

private theorem oddEndpoint_tendsto_atTop :
    Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop := by
  exact tendsto_atTop_add_const_right atTop (1 : ℝ)
    (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)

private theorem logAffine_mul_negative_rpow_tendsto_zero
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => (6400 + 48 * Real.log x) * x ^ (-ε))
      atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop hε
  have hlog := (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have hlogmul : Tendsto (fun x : ℝ => Real.log x * x ^ (-ε)) atTop (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hlim : Tendsto
      (fun x : ℝ => 6400 * x ^ (-ε) + 48 * (Real.log x * x ^ (-ε)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hpow.const_mul 6400).add (hlogmul.const_mul 48)
  exact hlim.congr' (Eventually.of_forall fun x => by ring)

/-- The source quotient envelope decays to zero. -/
theorem liClockPairedEtaSourceErrorEnvelope_tendsto_zero :
    Tendsto liClockPairedEtaSourceErrorEnvelope atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (6400 + 48 * Real.log (2 * (N : ℝ) + 1)) *
    (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0)
  exact (logAffine_mul_negative_rpow_tendsto_zero
    (by norm_num : 0 < (1 / 4 : ℝ))).comp oddEndpoint_tendsto_atTop

/-- Every sufficiently long prefix meets the finite denominator threshold. -/
theorem liClockPairedEta_eventually_valueTail_le_one_sixteenth :
    ∀ᶠ N : ℕ in atTop,
      3 * (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) ≤ 1 / 16 := by
  have hlim : Tendsto
      (fun N : ℕ => 3 * (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
        oddEndpoint_tendsto_atTop).const_mul 3
  exact (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16))).mono
    (fun _ hN => hN.le)

/-- Exact exponent bookkeeping for the logarithmically growing clock window. -/
theorem liClockPairedEtaSourceErrorEnvelope_mul_exp_eq_rpow
    (r c : ℝ) (N : ℕ) :
    liClockPairedEtaSourceErrorEnvelope N *
        Real.exp (c * Real.log (2 * (N : ℝ) + 1) / r) =
      (6400 + 48 * Real.log (2 * (N : ℝ) + 1)) *
        (2 * (N : ℝ) + 1) ^ (-(1 / 4 - c / r)) := by
  have ha : 0 < 2 * (N : ℝ) + 1 := by positivity
  have hexp : Real.exp (c * Real.log (2 * (N : ℝ) + 1) / r) =
      (2 * (N : ℝ) + 1) ^ (c / r) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
    ring
  unfold liClockPairedEtaSourceErrorEnvelope
  rw [hexp, mul_assoc, ← Real.rpow_add ha]
  congr 2
  ring

/-- The exponential clock envelope decays on every window `c * log (2N+1)` with `c < r/4`. -/
theorem liClockPairedEtaSourceErrorEnvelope_mul_exp_tendsto_zero
    {r c : ℝ} (hr : 0 < r) (_hc : 0 < c) (hcr : c < r / 4) :
    Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N *
      Real.exp (c * Real.log (2 * (N : ℝ) + 1) / r)) atTop (𝓝 0) := by
  have hε : 0 < (1 / 4 : ℝ) - c / r := by
    have hfrac : c / r < (1 / 4 : ℝ) :=
      (div_lt_iff₀ hr).2 (by nlinarith)
    linarith
  have hlim := (logAffine_mul_negative_rpow_tendsto_zero hε).comp
    oddEndpoint_tendsto_atTop
  apply hlim.congr'
  exact Eventually.of_forall fun N =>
    (liClockPairedEtaSourceErrorEnvelope_mul_exp_eq_rpow r c N).symm

/-- The sharper hyperbolic-sine clock envelope decays on the same growing windows. -/
theorem liClockPairedEtaSourceErrorEnvelope_mul_sinh_tendsto_zero
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (hcr : c < r / 4) :
    Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N *
      Real.sinh (c * Real.log (2 * (N : ℝ) + 1) / r)) atTop (𝓝 0) := by
  apply squeeze_zero _ _
    (liClockPairedEtaSourceErrorEnvelope_mul_exp_tendsto_zero hr hc hcr)
  · intro N
    apply mul_nonneg (liClockPairedEtaSourceErrorEnvelope_nonneg N)
    apply Real.sinh_nonneg_iff.mpr
    apply div_nonneg _ hr.le
    apply mul_nonneg hc.le
    exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  · intro N
    apply mul_le_mul_of_nonneg_left _ (liClockPairedEtaSourceErrorEnvelope_nonneg N)
    rw [Real.sinh_eq]
    have hpos := Real.exp_pos (c * Real.log (2 * (N : ℝ) + 1) / r)
    have hneg := Real.exp_pos (-(c * Real.log (2 * (N : ℝ) + 1) / r))
    linarith

end
end RHTower
