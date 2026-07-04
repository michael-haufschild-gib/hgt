/-
Doc 25 §1/§2 (task #143): the rescaled `q_d` arithmetic used in tracking clearance.

For `τ = a + bi`, the pair factor contributes

  `q_d(c) = |τ|^2 - 2 a d c + d(d-1)c^2`.

At the tracking scale `c = z/d`, this becomes

  `(z-a)^2 + b^2 - z^2/d`,

so on a bounded window `|z| ≤ R` it is bounded below by `b^2/2` as soon as
`d*b^2 ≥ 2R^2`.  This file banks that finite real-arithmetic input for doc 25
Theorem A; the analytic inputs (`Ã_d → g`, energy identity, nonvanishing) are separate
constraints, not a flow.
-/
import Mathlib

namespace RHTower

/-- The unscaled pair quadratic from doc 25: `q_d(c)`. -/
noncomputable def spurQ (a b : ℝ) (d : ℕ) (c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 - 2 * a * (d : ℝ) * c + (d : ℝ) * ((d : ℝ) - 1) * c ^ 2

/-- The tracking-scale form of `spurQ a b d (z/d)`. -/
noncomputable def spurQRescaled (a b : ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 - 2 * a * z + (1 - (1 : ℝ) / d) * z ^ 2

/-- Exact rescaling identity for `q_d(z/d)`. -/
theorem spurQ_rescale {a b z : ℝ} {d : ℕ} (hd : 0 < d) :
    spurQ a b d (z / (d : ℝ)) = spurQRescaled a b d z := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [spurQ, spurQRescaled]
  field_simp [hd0]

/-- Completing the square in the rescaled `q_d`. -/
theorem spurQRescaled_eq_sq (a b : ℝ) (d : ℕ) (z : ℝ) :
    spurQRescaled a b d z = (z - a) ^ 2 + b ^ 2 - z ^ 2 / (d : ℝ) := by
  rw [spurQRescaled]
  ring

/-- Doc 25 (E2): on `|z| ≤ R`, the rescaled pair quadratic is at least `b²/2`
once `d*b² ≥ 2R²`. -/
theorem spurQRescaled_lower_bound {a b R z : ℝ} {d : ℕ}
    (hdpos : 0 < d) (_hb : 0 < b) (hz : |z| ≤ R)
    (hd : 2 * R ^ 2 ≤ (d : ℝ) * b ^ 2) :
    b ^ 2 / 2 ≤ spurQRescaled a b d z := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hR0 : 0 ≤ R := le_trans (abs_nonneg z) hz
  have hzsq : z ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs z]
    nlinarith [hz, abs_nonneg z, hR0]
  have hdiv : z ^ 2 / (d : ℝ) ≤ b ^ 2 / 2 := by
    rw [div_le_iff₀ hd0]
    nlinarith [hzsq, hd]
  rw [spurQRescaled_eq_sq]
  have hsquare : 0 ≤ (z - a) ^ 2 := sq_nonneg _
  linarith

/-- Unscaled version of the tracking-window lower bound for `q_d(z/d)`. -/
theorem spurQ_rescaled_lower_bound {a b R z : ℝ} {d : ℕ}
    (hdpos : 0 < d) (hb : 0 < b) (hz : |z| ≤ R)
    (hd : 2 * R ^ 2 ≤ (d : ℝ) * b ^ 2) :
    b ^ 2 / 2 ≤ spurQ a b d (z / (d : ℝ)) := by
  rw [spurQ_rescale hdpos]
  exact spurQRescaled_lower_bound hdpos hb hz hd

/-- Doc 25 Theorem A arithmetic shell: a lower bound on `q` and an upper bound on the
energy denominator give the margin lower bound. -/
theorem theoremA_margin_lower_bound_arithmetic {q denom b m M R d : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hR : 0 < R) (hd : 0 < d)
    (hdenpos : 0 < denom)
    (hq : b ^ 2 / 2 ≤ q)
    (hden : denom ≤ 2 * (M + 1) * R ^ 4 / (m * d ^ 2)) :
    b ^ 2 * m * d ^ 2 / (4 * (M + 1) * R ^ 4) ≤ q / denom := by
  have hmdpos : 0 < m * d ^ 2 := by positivity
  have hden_cross : denom * (m * d ^ 2) ≤ 2 * (M + 1) * R ^ 4 := by
    rwa [le_div_iff₀ hmdpos] at hden
  have hfourpos : 0 < 4 * (M + 1) * R ^ 4 := by positivity
  rw [le_div_iff₀ hdenpos]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ hfourpos]
  nlinarith [hden_cross, hq, sq_nonneg b]

/-- Tracking-window form of the Theorem A arithmetic shell, with `q = q_d(z/d)`. -/
theorem theoremA_margin_lower_bound_from_tracking {a b R z denom m M : ℝ} {d : ℕ}
    (hdpos : 0 < d) (hb : 0 < b) (hm : 0 < m) (hM : 0 ≤ M) (hR : 0 < R)
    (hz : |z| ≤ R)
    (hdsize : 2 * R ^ 2 ≤ (d : ℝ) * b ^ 2)
    (hdenpos : 0 < denom)
    (hden : denom ≤ 2 * (M + 1) * R ^ 4 / (m * (d : ℝ) ^ 2)) :
    b ^ 2 * m * (d : ℝ) ^ 2 / (4 * (M + 1) * R ^ 4)
      ≤ spurQ a b d (z / (d : ℝ)) / denom := by
  exact theoremA_margin_lower_bound_arithmetic (q := spurQ a b d (z / (d : ℝ)))
    (denom := denom) (b := b) (m := m) (M := M) (R := R) (d := (d : ℝ))
    hm hM hR (by positivity) hdenpos (spurQ_rescaled_lower_bound hdpos hb hz hdsize) hden

/-- Completing the square for the unscaled `q_d`; the dip is at `c = a/(d-1)`. -/
theorem spurQ_eq_sq_about_dip {a b c : ℝ} {d : ℕ} (hd : 1 < d) :
    spurQ a b d c = (d : ℝ) * ((d : ℝ) - 1) * (c - a / ((d : ℝ) - 1)) ^ 2
      + b ^ 2 - a ^ 2 / ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hD : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [spurQ]
  field_simp [hD]
  ring

/-- The value of `q_d` at its dip point. -/
theorem spurQ_dip_value {a b : ℝ} {d : ℕ} (hd : 1 < d) :
    spurQ a b d (a / ((d : ℝ) - 1)) = b ^ 2 - a ^ 2 / ((d : ℝ) - 1) := by
  rw [spurQ_eq_sq_about_dip hd]
  ring

/-- Doc 25 Corollary C arithmetic: for `d ≥ 2`, the rescaled dip location
`ad/(d-1)` lies within `2|a|`. -/
theorem dip_rescaled_abs_le_two_abs {a : ℝ} {d : ℕ} (hd : 2 ≤ d) :
    |a * (d : ℝ) / ((d : ℝ) - 1)| ≤ 2 * |a| := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hpos : 0 < (d : ℝ) - 1 := lt_of_lt_of_le zero_lt_one hd1
  have hratio : (d : ℝ) / ((d : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hd1]
  have hratio_nonneg : 0 ≤ (d : ℝ) / ((d : ℝ) - 1) := by positivity
  have hrewrite : a * (d : ℝ) / ((d : ℝ) - 1) = a * ((d : ℝ) / ((d : ℝ) - 1)) := by
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg hratio_nonneg]
  nlinarith [abs_nonneg a, hratio]

/-- If the tracking window radius is larger than `2|a|`, the dip point is inside it. -/
theorem dip_rescaled_mem_tracking_window {a R : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hR : 2 * |a| < R) :
    |a * (d : ℝ) / ((d : ℝ) - 1)| < R := by
  exact lt_of_le_of_lt (dip_rescaled_abs_le_two_abs (a := a) hd) hR

end RHTower
