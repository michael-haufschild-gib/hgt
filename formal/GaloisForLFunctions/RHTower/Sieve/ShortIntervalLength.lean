import GaloisForLFunctions.RHTower.Sieve.LogPowerLimits

/-!
# The short-interval length of the Route E cards

The cards fix `h(x) = exp((log x)^β)` with `1/2 < β < 1`.  This file records the three facts every
capstone of the reduction asks of that function: its logarithm, that it grows, and that it stays
below `√x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The cards' short-interval length. -/
def cardLength (β x : ℝ) : ℝ := Real.exp ((Real.log x) ^ β)

theorem cardLength_pos (β x : ℝ) : 0 < cardLength β x := Real.exp_pos _

theorem log_cardLength (β x : ℝ) : Real.log (cardLength β x) = (Real.log x) ^ β := by
  rw [cardLength, Real.log_exp]

/-- **The short-interval length grows.** -/
theorem tendsto_cardLength {β : ℝ} (hβ : 0 < β) :
    Tendsto (cardLength β) atTop atTop := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  exact Real.tendsto_exp_atTop.comp hpow

/-- **The short-interval length stays below `√x`.**  `(log x)^β ≤ (log x)/2` once
`log x ≥ 2^{1/(1−β)}`. -/
theorem cardLength_le_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, cardLength β x ≤ Real.sqrt x := by
  have hgrow : Tendsto (fun x : ℝ => (Real.log x) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - β)).comp Real.tendsto_log_atTop
  filter_upwards [hgrow.eventually_ge_atTop (2 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hsplit : (Real.log x) ^ β * (Real.log x) ^ (1 - β) = Real.log x := by
    rw [← Real.rpow_add hlog]
    norm_num
  have hpow0 : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlog _
  have hle : (Real.log x) ^ β ≤ Real.log x / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hsplit, hx, hpow0]
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [cardLength, hsqrt]
  exact Real.exp_le_exp.2 hle

end

end RHTower.Sieve
