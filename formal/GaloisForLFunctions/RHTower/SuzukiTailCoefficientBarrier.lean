import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The coefficient price of a tail reconstruction

Tail completeness is free of coefficient control, and the ridge penalty is the only term that sees
that cost.  Making the cost explicit is one Cauchy–Schwarz step: a tail-supported synthesis that
reproduces the unit source to within `1/4` must pair with the *analysis* tail vector at strength
above `3/4`, so its coefficient norm is at least `3/(4‖u_H‖)`.  Since the analysis tail is
`O(log T/T)`, the coefficient norm squared is at least of order `T/log T`.

Multiplying by the ridge mass gives the barrier `rT/log(T+2) = O(1)`, which the card's cutoff
`T = r^{-4}` violates: there `rT/log(T+2)` is of order `r^{-3}/log(r^{-1})`, and that diverges.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(399)`: the ridge penalty of a good approximation -/

/-- **`(399)`: a small enough ridge mass keeps the regularized defect near the approximation
defect.** -/
theorem tikhonov_lt_of_small_ridge {ε r d cn : ℝ} (hε : 0 < ε) (hd0 : 0 ≤ d) (hd : d < ε)
    (hcn : 0 ≤ cn) (hr0 : 0 < r) (hr : r < ε ^ (2 : ℕ) / (1 + cn)) :
    d ^ (2 : ℕ) + r * cn < 2 * ε ^ (2 : ℕ) := by
  have h1c : (0 : ℝ) < 1 + cn := by linarith
  have hd2 : d ^ (2 : ℕ) < ε ^ (2 : ℕ) := by nlinarith
  have hrc : r * cn < ε ^ (2 : ℕ) := by
    have hmul : r * (1 + cn) < ε ^ (2 : ℕ) := by
      rw [lt_div_iff₀ h1c] at hr
      linarith
    nlinarith [hmul, hr0, hcn]
  linarith

/-! ## `(401)`: the coefficient price -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The synthesis pairs strongly with the source. -/
theorem inner_gt_of_small_defect {h p : E} (hh : ‖h‖ = 1) (hd : ‖h - p‖ < 1 / 4) :
    3 / 4 < (inner ℝ h p : ℝ) := by
  have hsplit : (inner ℝ h p : ℝ) = ‖h‖ ^ (2 : ℕ) - inner ℝ h (h - p) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hcs : (inner ℝ h (h - p) : ℝ) ≤ ‖h‖ * ‖h - p‖ :=
    real_inner_le_norm h (h - p)
  rw [hsplit, hh] at *
  nlinarith [hcs, hd]

/-- **`(401)`: the coefficient norm of a tail synthesis is bounded below by the reciprocal analysis
tail.** -/
theorem coefficient_norm_sq_gt {h p uH c : E} (hh : ‖h‖ = 1) (hd : ‖h - p‖ < 1 / 4)
    (hpair : (inner ℝ h p : ℝ) = inner ℝ uH c) (huH : 0 < ‖uH‖) :
    (3 / 4) ^ (2 : ℕ) / ‖uH‖ ^ (2 : ℕ) < ‖c‖ ^ (2 : ℕ) := by
  have hgt : 3 / 4 < (inner ℝ uH c : ℝ) := by
    rw [← hpair]
    exact inner_gt_of_small_defect hh hd
  have hcs : (inner ℝ uH c : ℝ) ≤ ‖uH‖ * ‖c‖ := real_inner_le_norm uH c
  have hcpos : 0 < ‖c‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hc0 : ‖c‖ = 0 := le_antisymm hcon (norm_nonneg _)
    rw [hc0, mul_zero] at hcs
    linarith
  have hlin : 3 / 4 < ‖uH‖ * ‖c‖ := lt_of_lt_of_le hgt hcs
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hlin, huH, hcpos]

/-- **`(401)`, with the analysis tail bound inserted.** -/
theorem coefficient_price {cn uHsq C T logT : ℝ} (hC : 0 < C) (hT : 0 < T) (hlog : 0 < logT)
    (huposs : 0 < uHsq) (hu : uHsq ≤ C * logT / T) (hc : (3 / 4) ^ (2 : ℕ) / uHsq < cn) :
    9 / (16 * C) * (T / logT) < cn := by
  have hstep : 9 / (16 * C) * (T / logT) ≤ (3 / 4) ^ (2 : ℕ) / uHsq := by
    have hL : 9 / (16 * C) * (T / logT) = 9 * T / (16 * C * logT) := by
      field_simp
    have hR : ((3 : ℝ) / 4) ^ (2 : ℕ) / uHsq = 9 / (16 * uHsq) := by
      field_simp
      ring
    rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    have hCT : uHsq * T ≤ C * logT := by
      rw [le_div_iff₀ hT] at hu
      linarith
    nlinarith [hCT, huposs, hT, hC, hlog]
  linarith

/-! ## `(402)`–`(403)`: the moving-scale barrier -/

/-- **`(402)`: the ridge penalty bounds the tail cutoff.** -/
theorem ridge_cutoff_bound {r cn C T logT : ℝ} (hr : 0 < r) (hC : 0 < C) (hT : 0 < T)
    (hlog : 0 < logT) (hJ : r * cn < 1 / 16)
    (hcn : 9 / (16 * C) * (T / logT) ≤ cn) :
    r * (T / logT) < C / 9 := by
  have hpos : 0 < T / logT := div_pos hT hlog
  have hmul : r * (9 / (16 * C) * (T / logT)) ≤ r * cn := mul_le_mul_of_nonneg_left hcn hr.le
  have hchain : r * (9 / (16 * C) * (T / logT)) < 1 / 16 := lt_of_le_of_lt hmul hJ
  have hexp : r * (9 / (16 * C) * (T / logT)) = 9 / (16 * C) * (r * (T / logT)) := by ring
  rw [hexp] at hchain
  have hcoef : 0 < 9 / (16 * C) := by positivity
  by_contra hcon
  rw [not_lt] at hcon
  have hge : 9 / (16 * C) * (C / 9) ≤ 9 / (16 * C) * (r * (T / logT)) :=
    mul_le_mul_of_nonneg_left hcon hcoef.le
  have hval : 9 / (16 * C) * (C / 9) = 1 / 16 := by
    field_simp
  rw [hval] at hge
  linarith

/-- The cubic-over-logarithm rate diverges, which is what kills the cutoff `T = r^{-4}`. -/
theorem tendsto_cube_div_log_atTop :
    Tendsto (fun x : ℝ => x ^ (3 : ℕ) / Real.log x) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_pow_atTop (n := 2) (by norm_num))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hle : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
    linarith
  rw [le_div_iff₀ hlog]
  nlinarith [hle, hlog, hx]

end GaloisForLFunctions.RHTower
