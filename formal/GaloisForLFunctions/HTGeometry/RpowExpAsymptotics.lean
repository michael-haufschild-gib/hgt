import Mathlib

/-!
# Two eventual comparisons for real powers

The parameter choice in a Wiman--Valiron argument needs exactly two asymptotic facts, both in the
"eventually" form rather than the limit form:

* a stretched exponential `exp(c t^δ)` eventually dominates every constant multiple of a power;
* a power `t^γ` with `γ < 1`, even multiplied by a logarithm, is eventually a small multiple of `t`.

Both are consequences of mathlib's `tendsto_exp_div_rpow_atTop` and `isLittleO_log_rpow_atTop`, but
neither is available in the eventual-inequality shape that a parameter verification uses.
-/

open Filter Asymptotics
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- **A stretched exponential dominates every power.**  For `c, δ > 0` and any exponent `p` and any
constant `C`, eventually `C t^p ≤ exp (c t^δ)`. -/
theorem eventually_mul_rpow_le_exp_rpow (C : ℝ) {c δ p : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, C * t ^ p ≤ Real.exp (c * t ^ δ) := by
  have hbase : Tendsto (fun t : ℝ => c * t ^ δ) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (tendsto_rpow_atTop hδ)
  have hmain := (tendsto_exp_div_rpow_atTop (p / δ)).comp hbase
  have hcoef : (0 : ℝ) < c ^ (p / δ) := Real.rpow_pos_of_pos hc _
  have hev := hmain.eventually_ge_atTop ((|C| + 1) / c ^ (p / δ))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  simp only [Function.comp] at ht
  have hrw : (c * t ^ δ) ^ (p / δ) = c ^ (p / δ) * t ^ p := by
    rw [Real.mul_rpow (le_of_lt hc) (Real.rpow_nonneg (le_of_lt htpos) δ),
      ← Real.rpow_mul (le_of_lt htpos)]
    congr 1
    field_simp
  rw [hrw] at ht
  have htp : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos htpos p
  have hpos : (0 : ℝ) < c ^ (p / δ) * t ^ p := by positivity
  have h1 : ((|C| + 1) / c ^ (p / δ)) * (c ^ (p / δ) * t ^ p)
      ≤ (Real.exp (c * t ^ δ) / (c ^ (p / δ) * t ^ p)) * (c ^ (p / δ) * t ^ p) :=
    mul_le_mul_of_nonneg_right ht (le_of_lt hpos)
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h1
  have h2 : ((|C| + 1) / c ^ (p / δ)) * (c ^ (p / δ) * t ^ p) = (|C| + 1) * t ^ p := by
    field_simp
  rw [h2] at h1
  have h3 : C ≤ |C| + 1 := by
    have := le_abs_self C
    linarith
  nlinarith [h1, htp, h3]

/-- **A subunit power times a logarithm is eventually a small multiple of the variable.**  For
`γ < 1` and every `ε > 0` and every constant `C`, eventually `C t^γ log t ≤ ε t`. -/
theorem eventually_mul_rpow_log_le (C : ℝ) {γ ε : ℝ} (hγ : γ < 1) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, C * (t ^ γ * Real.log t) ≤ ε * t := by
  have hgap : (0 : ℝ) < 1 - γ := by linarith
  have hlog : Real.log =o[atTop] fun t : ℝ => t ^ (1 - γ) := isLittleO_log_rpow_atTop hgap
  have hmul : (fun t : ℝ => t ^ γ * Real.log t) =o[atTop] fun t : ℝ => t ^ γ * t ^ (1 - γ) :=
    (isBigO_refl (fun t : ℝ => t ^ γ) atTop).mul_isLittleO hlog
  have hcongr : (fun t : ℝ => t ^ γ * t ^ (1 - γ)) =ᶠ[atTop] fun t : ℝ => t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht, show γ + (1 - γ) = (1 : ℝ) by ring, Real.rpow_one]
  have hfin : (fun t : ℝ => t ^ γ * Real.log t) =o[atTop] fun t : ℝ => t :=
    hmul.trans_eventuallyEq hcongr
  have hdef := hfin.def (show (0 : ℝ) < ε / (|C| + 1) by positivity)
  filter_upwards [hdef, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hnorm : ‖t‖ = t := by
    rw [Real.norm_eq_abs, abs_of_pos htpos]
  rw [hnorm] at ht
  have habs : C * (t ^ γ * Real.log t) ≤ |C| * ‖t ^ γ * Real.log t‖ := by
    calc C * (t ^ γ * Real.log t) ≤ |C * (t ^ γ * Real.log t)| := le_abs_self _
      _ = |C| * |t ^ γ * Real.log t| := abs_mul _ _
      _ = |C| * ‖t ^ γ * Real.log t‖ := by rw [Real.norm_eq_abs]
  have hC0 : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hstep : |C| * ‖t ^ γ * Real.log t‖ ≤ |C| * (ε / (|C| + 1) * t) :=
    mul_le_mul_of_nonneg_left ht hC0
  have hfrac : |C| * (ε / (|C| + 1) * t) ≤ ε * t := by
    have hden : (0 : ℝ) < |C| + 1 := by linarith
    have hratio : |C| / (|C| + 1) ≤ 1 := by
      rw [div_le_one hden]
      linarith
    have heq : |C| * (ε / (|C| + 1) * t) = (|C| / (|C| + 1)) * (ε * t) := by
      field_simp
    rw [heq]
    have hεt : (0 : ℝ) ≤ ε * t := by positivity
    nlinarith [hratio, hεt]
  linarith

/-! ## The Wiman--Valiron parameter conditions -/

/-- **The tail condition holds eventually.**  With the scale `s = t^β` and the window
`H = t^{-α} s / (8t)`, the condition `(1 + 4/H)^(3 : ℕ) e^{-sH/2} ≤ 1` holds for all large `t` exactly
because `sH/2 = t^{2β-α-1}/16` has a positive exponent while `4/H = 32 t^{1+α-β}` is only a
power. -/
theorem eventually_tail_condition {α β : ℝ} (hα : 0 < α) (hβ1 : β ≤ 1) (hlow : 1 + α < 2 * β) :
    ∀ᶠ t : ℝ in atTop,
      (1 + 4 / (t ^ (-α) * t ^ β / (8 * t))) ^ 3
        * Real.exp (-(t ^ β * (t ^ (-α) * t ^ β / (8 * t)) / 2)) ≤ 1 := by
  have hκ : (0 : ℝ) < 1 + α - β := by linarith
  have hδ0 : (0 : ℝ) < 2 * β - α - 1 := by linarith
  have hmain := eventually_mul_rpow_le_exp_rpow (C := 35937) (c := 1 / 16)
    (δ := 2 * β - α - 1) (p := 3 * (1 + α - β)) (by norm_num) hδ0
  filter_upwards [hmain, eventually_ge_atTop (1 : ℝ)] with t hmain' ht1
  have htpos : (0 : ℝ) < t := by linarith
  -- the window in closed form
  have h1 : t ^ (-α) * t ^ β = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have h2 : t ^ (β - α - 1) * t ^ (1 : ℝ) = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [Real.rpow_one] at h2
  have hH : t ^ (-α) * t ^ β / (8 * t) = t ^ (β - α - 1) / 8 := by
    rw [h1, ← h2]
    field_simp
  rw [hH]
  -- the reciprocal window
  have hneg : t ^ (β - α - 1) = (t ^ (1 + α - β))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt htpos)]
    congr 1
    ring
  have hxpos : (0 : ℝ) < t ^ (1 + α - β) := Real.rpow_pos_of_pos htpos _
  have hinv : 4 / (t ^ (β - α - 1) / 8) = 32 * t ^ (1 + α - β) := by
    rw [hneg]
    field_simp
    norm_num
  -- the exponent
  have h4 : t ^ β * t ^ (β - α - 1) = t ^ (2 * β - α - 1) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have hexpo : t ^ β * (t ^ (β - α - 1) / 8) / 2 = 1 / 16 * t ^ (2 * β - α - 1) := by
    rw [← h4]
    ring
  rw [hinv, hexpo]
  -- the polynomial bound on the amplification
  have hone : (1 : ℝ) ≤ t ^ (1 + α - β) := by
    have h0 : t ^ (0 : ℝ) ≤ t ^ (1 + α - β) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (le_of_lt hκ)
    rwa [Real.rpow_zero] at h0
  have hcube : (t ^ (1 + α - β)) ^ (3 : ℕ) = t ^ (3 * (1 + α - β)) := by
    rw [← Real.rpow_natCast (t ^ (1 + α - β)) 3, ← Real.rpow_mul (le_of_lt htpos)]
    congr 1
    push_cast
    ring
  have hpoly : (1 + 32 * t ^ (1 + α - β)) ^ 3 ≤ 35937 * t ^ (3 * (1 + α - β)) := by
    have hstep : (1 + 32 * t ^ (1 + α - β)) ^ 3 ≤ (33 * t ^ (1 + α - β)) ^ 3 := by
      have hb : 1 + 32 * t ^ (1 + α - β) ≤ 33 * t ^ (1 + α - β) := by linarith
      have hnn : (0 : ℝ) ≤ 1 + 32 * t ^ (1 + α - β) := by positivity
      gcongr
    calc (1 + 32 * t ^ (1 + α - β)) ^ 3 ≤ (33 * t ^ (1 + α - β)) ^ 3 := hstep
      _ = 35937 * (t ^ (1 + α - β)) ^ (3 : ℕ) := by ring
      _ = 35937 * t ^ (3 * (1 + α - β)) := by rw [hcube]
  -- conclude
  have hexppos : (0 : ℝ) < Real.exp (1 / 16 * t ^ (2 * β - α - 1)) := Real.exp_pos _
  have hle : (1 + 32 * t ^ (1 + α - β)) ^ 3 ≤ Real.exp (1 / 16 * t ^ (2 * β - α - 1)) :=
    le_trans hpoly hmain'
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ hexppos]
  simpa using hle

/-- **A subunit power is eventually a small multiple of the variable.** -/
theorem eventually_mul_rpow_le (C : ℝ) {γ ε : ℝ} (hγ : γ < 1) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, C * t ^ γ ≤ ε * t := by
  have hgap : (0 : ℝ) < 1 - γ := by linarith
  have htend : Tendsto (fun t : ℝ => t ^ (-(1 - γ))) atTop (nhds 0) := tendsto_rpow_neg_atTop hgap
  have hev := htend.eventually_le_const (show (0 : ℝ) < ε / (|C| + 1) by positivity)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hsplit : t ^ γ = t ^ (-(1 - γ)) * t := by
    have h1 : t ^ (-(1 - γ)) * t ^ (1 : ℝ) = t ^ γ := by
      rw [← Real.rpow_add htpos]
      congr 1
      ring
    rw [Real.rpow_one] at h1
    exact h1.symm
  have hC : C ≤ |C| + 1 := by
    have := le_abs_self C
    linarith
  have hpow0 : (0 : ℝ) < t ^ (-(1 - γ)) := Real.rpow_pos_of_pos htpos _
  have hpowγ : (0 : ℝ) < t ^ γ := Real.rpow_pos_of_pos htpos _
  calc C * t ^ γ ≤ (|C| + 1) * t ^ γ := by nlinarith [hpowγ, hC]
    _ = (|C| + 1) * (t ^ (-(1 - γ)) * t) := by rw [hsplit]
    _ ≤ (|C| + 1) * ((ε / (|C| + 1)) * t) := by
        have hden : (0 : ℝ) < |C| + 1 := by positivity
        have : t ^ (-(1 - γ)) * t ≤ (ε / (|C| + 1)) * t :=
          mul_le_mul_of_nonneg_right ht (le_of_lt htpos)
        nlinarith [this, hden]
    _ = ε * t := by field_simp

/-- **The main term and the logarithmic correction are eventually small.**  With the scale
`s = t^β` and the window `H = t^{-α} s/(8t)`, the closed-form Wiman--Valiron bound is below `ε(t-1)`
for all large `t`, uniformly in a logarithm argument that is at most `21t`. -/
theorem eventually_smallness {α β ε : ℝ} (hα : 0 < α) (hβ23 : β < 2 / 3)
    (hαβ : α < β / 2) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ A : ℝ, 1 ≤ A → A ≤ 21 * t →
      49 * (t ^ β * Real.sqrt (t ^ β))
        + 20 * Real.sqrt (t ^ β) * Real.log A / (t ^ (-α) * t ^ β / (8 * t))
        ≤ ε * (t - 1) := by
  have hγ1 : 3 * β / 2 < 1 := by linarith
  have hγ2 : 1 + α - β / 2 < 1 := by linarith
  have hmain := eventually_mul_rpow_le 49 (γ := 3 * β / 2) hγ1 (show (0:ℝ) < ε / 4 by positivity)
  have hlog1 := eventually_mul_rpow_le (160 * Real.log 21) (γ := 1 + α - β / 2) hγ2
    (show (0:ℝ) < ε / 4 by positivity)
  have hlog2 := eventually_mul_rpow_log_le 160 (γ := 1 + α - β / 2) hγ2
    (show (0:ℝ) < ε / 4 by positivity)
  filter_upwards [hmain, hlog1, hlog2, eventually_ge_atTop (4 : ℝ)] with
    t hmain' hlog1' hlog2' ht4
  intro A hA1 hA21
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  -- the square root of the scale
  have hsqrt : Real.sqrt (t ^ β) = t ^ (β / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt htpos)]
    congr 1
    ring
  -- the main term
  have hfirst : 49 * (t ^ β * Real.sqrt (t ^ β)) = 49 * t ^ (3 * β / 2) := by
    rw [hsqrt, ← Real.rpow_add htpos]
    congr 2
    ring
  -- the window in closed form
  have h1 : t ^ (-α) * t ^ β = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have h2 : t ^ (β - α - 1) * t ^ (1 : ℝ) = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [Real.rpow_one] at h2
  have hH : t ^ (-α) * t ^ β / (8 * t) = t ^ (β - α - 1) / 8 := by
    rw [h1, ← h2]
    field_simp
  have hneg : t ^ (β - α - 1) = (t ^ (1 + α - β))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt htpos)]
    congr 1
    ring
  have hxpos : (0 : ℝ) < t ^ (1 + α - β) := Real.rpow_pos_of_pos htpos _
  have hmerge : t ^ (β / 2) * t ^ (1 + α - β) = t ^ (1 + α - β / 2) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have hsecond : 20 * Real.sqrt (t ^ β) * Real.log A / (t ^ (-α) * t ^ β / (8 * t))
      = 160 * (t ^ (1 + α - β / 2) * Real.log A) := by
    rw [hH, hsqrt, hneg, ← hmerge]
    field_simp
    ring
  -- the logarithm is bounded by that of `21 t`
  have hlogA : Real.log A ≤ Real.log 21 + Real.log t := by
    have hle : Real.log A ≤ Real.log (21 * t) := Real.log_le_log (by linarith) hA21
    rwa [Real.log_mul (by norm_num) (ne_of_gt htpos)] at hle
  have hlogA0 : (0 : ℝ) ≤ Real.log A := Real.log_nonneg hA1
  have hpow0 : (0 : ℝ) < t ^ (1 + α - β / 2) := Real.rpow_pos_of_pos htpos _
  have hbound : 160 * (t ^ (1 + α - β / 2) * Real.log A)
      ≤ 160 * Real.log 21 * t ^ (1 + α - β / 2) + 160 * (t ^ (1 + α - β / 2) * Real.log t) := by
    nlinarith [hlogA, hpow0]
  have hεt : ε * 4 ≤ ε * t := mul_le_mul_of_nonneg_left ht4 (le_of_lt hε)
  rw [hfirst, hsecond]
  linarith

/-- The window `t^{-α} t^β / (8t)` times `t - 1` is at least `t^{β-α}/16`. -/
theorem sub_one_mul_window_ge {t α β : ℝ} (ht2 : 2 ≤ t) :
    t ^ (β - α) / 16 ≤ (t - 1) * (t ^ (-α) * t ^ β / (8 * t)) := by
  have htpos : (0 : ℝ) < t := by linarith
  have h1 : t ^ (-α) * t ^ β = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have h2 : t ^ (β - α - 1) * t ^ (1 : ℝ) = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [Real.rpow_one] at h2
  have hH : t ^ (-α) * t ^ β / (8 * t) = t ^ (β - α - 1) / 8 := by
    rw [h1, ← h2]
    field_simp
  have hpow : (0 : ℝ) < t ^ (β - α - 1) := Real.rpow_pos_of_pos htpos _
  rw [hH, ← h2]
  nlinarith [hpow, ht2]

end GaloisForLFunctions.HTGeometry
