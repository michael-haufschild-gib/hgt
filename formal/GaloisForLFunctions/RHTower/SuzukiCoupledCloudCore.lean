import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The coefficient scale of a ridge certificate and the coupled-gain floor

The ridge term of the objective is the only control on the coefficient norm, and it is sharp: an
objective below `1/16` forces `‖c‖ < 1/(4√r)`.  Paired against the analysis tail, that scale is
exactly what makes the high-side correlation `√(C log H/(16 r H))`, which vanishes precisely under
the card's cutoff condition.

On the coupled branch the same scale appears from the other side.  Positivity of the complementary
Schur block below the ridge mass turns an order-one gain into an order-`√r` residual, and the
reverse triangle inequality against a negligible analysis tail transfers that residual to the
leakage of the low-only optimizer.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(416)`: the coefficient scale -/

/-- **`(416)`: the ridge penalty pins the coefficient norm to the scale `1/√r`.** -/
theorem coefficient_norm_lt_of_objective {r cn : ℝ} (hr : 0 < r)
    (hJ : r * cn ^ 2 < 1 / 16) : cn < 1 / (4 * Real.sqrt r) := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : (1 / (4 * Real.sqrt r)) ^ 2 = 1 / (16 * r) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hr.le]
    norm_num
  have h1 : cn ^ 2 < (1 / (4 * Real.sqrt r)) ^ 2 := by
    rw [hsq, lt_div_iff₀ (by positivity)]
    nlinarith [hJ]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1

/-! ## `(417)`: the high-side correlation -/

/-- **`(417)`: the high-side pairing is at most the explicit tail/ridge quantity.** -/
theorem highSide_pairing_le {uH cn C logH H r : ℝ} (hr : 0 < r) (hH : 0 < H)
    (hClog : 0 ≤ C * logH) (hcn0 : 0 ≤ cn)
    (huH : uH ≤ Real.sqrt (C * logH / H)) (hcn : cn ≤ 1 / (4 * Real.sqrt r)) :
    uH * cn ≤ Real.sqrt (C * logH / (16 * r * H)) := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hquot : (0 : ℝ) ≤ C * logH / H := div_nonneg hClog hH.le
  have hkey : Real.sqrt (C * logH / (16 * r * H))
      = Real.sqrt (C * logH / H) / (4 * Real.sqrt r) := by
    have hrw : C * logH / (16 * r * H) = (C * logH / H) / (16 * r) := by
      field_simp
    rw [hrw, Real.sqrt_div hquot, show (16 : ℝ) * r = 4 ^ 2 * r by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  rw [hkey]
  have hmul : uH * cn ≤ Real.sqrt (C * logH / H) * (1 / (4 * Real.sqrt r)) := by
    refine mul_le_mul huH hcn hcn0 (Real.sqrt_nonneg _)
  calc uH * cn ≤ Real.sqrt (C * logH / H) * (1 / (4 * Real.sqrt r)) := hmul
    _ = Real.sqrt (C * logH / H) / (4 * Real.sqrt r) := by ring

/-! ## `(410)`: the coupled-gain floor -/

/-- **`(410)`, middle: an order-one Schur gain forces an order-`r` residual.** -/
theorem residual_sq_gt_of_gain {χ e r : ℝ} (hr : 0 < r) (hχ : 1 / 16 < χ) (hle : χ ≤ e / r) :
    r / 16 < e := by
  rw [le_div_iff₀ hr] at hle
  nlinarith [hχ, hr, hle]

/-- **`(410)`, last: the leakage of the low-only optimizer inherits the residual scale.** -/
theorem leak_norm_gt {E : Type*} [NormedAddCommGroup E] {eH uH v : E} {r : ℝ}
    (hr : 0 < r) (heq : eH = uH - v)
    (hres : Real.sqrt r / 4 < ‖eH‖) (hsmall : ‖uH‖ ≤ Real.sqrt r / 16) :
    Real.sqrt r / 8 < ‖v‖ := by
  have hv : v = uH - eH := by
    rw [heq]
    abel
  have htri : ‖eH‖ ≤ ‖uH‖ + ‖v‖ := by
    calc ‖eH‖ = ‖uH - v‖ := by rw [heq]
      _ ≤ ‖uH‖ + ‖v‖ := norm_sub_le _ _
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  linarith

end GaloisForLFunctions.RHTower
