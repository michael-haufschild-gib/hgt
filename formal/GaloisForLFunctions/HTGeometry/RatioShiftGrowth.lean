import Mathlib

/-!
# Divergent ratio survives a constant shift

If a sequence `b` diverges to `+∞` with divergent successive ratio `b(n+1)/b n → +∞`, then
subtracting a fixed nonnegative constant preserves both: `(b(n+1)-c)/(b n - c) → +∞`
(`ratio_sub_nonneg_const_tendsto_atTop`).  The shifted ratio dominates `(b(n+1)-c)/b n`, which
is `b(n+1)/b n` minus a null term.

Instantiated at an integer exponent sequence and `c = j`, this says the exponent gaps of a
superlacunary series are inherited by its `j`-th formal derivative: the derivative is again
superlacunary with divergent ratio, the analytic counterpart of the support shift.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- **Divergent ratio under a constant shift.**  Subtracting a nonnegative constant preserves
a divergent successive ratio. -/
theorem ratio_sub_nonneg_const_tendsto_atTop {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    (hr : Tendsto (fun n => b (n + 1) / b n) atTop atTop) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n => (b (n + 1) - c) / (b n - c)) atTop atTop := by
  have hcinv : Tendsto (fun n => -(c * (b n)⁻¹)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := c)).mul hb.inv_tendsto_atTop
    simpa using h.neg
  have hlow : Tendsto (fun n => b (n + 1) / b n + -(c * (b n)⁻¹)) atTop atTop :=
    hr.atTop_add hcinv
  have hbc : ∀ᶠ n in atTop, c < b n := hb.eventually_gt_atTop c
  have hbc1 : ∀ᶠ n in atTop, c ≤ b (n + 1) :=
    (hb.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop c
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [hbc, hbc1] with n hn hn1
  have hbn : 0 < b n := lt_of_le_of_lt hc hn
  have hbnc : 0 < b n - c := by linarith
  calc b (n + 1) / b n + -(c * (b n)⁻¹)
      = (b (n + 1) - c) / b n := by field_simp; ring
    _ ≤ (b (n + 1) - c) / (b n - c) :=
        div_le_div_of_nonneg_left (by linarith) hbnc (by linarith)

end GaloisForLFunctions
