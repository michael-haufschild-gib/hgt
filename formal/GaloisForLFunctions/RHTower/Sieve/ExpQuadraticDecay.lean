import GaloisForLFunctions.RHTower.Sieve.MoebiusMajorantRatio

/-!
# Linear growth against quadratic decay

The price of narrow smoothing is `exp(2(log N)^{1/20})` and the saving is
`exp(-c₀(log N)^{1/10}/8192)`.  Writing `v = (log N)^{1/20}` the second exponent is `-c₀v²/8192`,
because `(u^{1/20})² = u^{1/10}` — so the comparison is between a linear and a quadratic function of
a single variable, and the quadratic wins.

This is the reason `1/20` is the right choice for the smoothing exponent: any exponent strictly
below `1/10` would do, and halving it makes the comparison exactly the elementary one below.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The twentieth root squared is the tenth root. -/
theorem rpow_twentieth_sq {u : ℝ} (hu : 0 ≤ u) :
    (u ^ ((1 : ℝ) / 20)) ^ 2 = u ^ ((1 : ℝ) / 10) := by
  rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 20)) 2, ← Real.rpow_mul hu]
  norm_num

/-- **Linear growth loses to quadratic decay.** -/
theorem tendsto_exp_two_sub_sq {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun v : ℝ => Real.exp (2 * v - κ * v ^ 2)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun v => (Real.exp_pos _).le) ?_
    Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_ge_atTop (3 / κ), eventually_ge_atTop (0 : ℝ)] with v hv hv0
  refine Real.exp_le_exp.2 ?_
  have hκv : (3 : ℝ) ≤ κ * v := by
    rw [div_le_iff₀ hκ] at hv
    linarith
  nlinarith [hv0, hκv]

/-- **The combined comparison.**  A polynomial in `v²` times the price `exp(2v)` still loses to the
saving `exp(-κv²)`, since the surviving exponent is `2v - κv²`. -/
theorem tendsto_poly_exp_two_sub_sq {a b c κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun v : ℝ =>
        (1 + a * (v ^ 2) ^ 9) * (b + c * v ^ 2) * Real.exp (2 * v) * Real.exp (-(κ * v ^ 2)))
      atTop (𝓝 0) := by
  have hquad : Tendsto (fun v : ℝ => v ^ 2) atTop atTop :=
    tendsto_pow_atTop (α := ℝ) (by norm_num)
  have hbase : Tendsto (fun w : ℝ =>
      (1 + a * w ^ 9) * (b + c * w) * Real.exp (-(κ / 2 * w))) atTop (𝓝 0) :=
    tendsto_polyEdge_mul_exp_neg (by positivity)
  have hcomp : Tendsto (fun v : ℝ =>
      (1 + a * (v ^ 2) ^ 9) * (b + c * v ^ 2) * Real.exp (-(κ / 2 * v ^ 2)))
      atTop (𝓝 0) := hbase.comp hquad
  have hrest : Tendsto (fun v : ℝ => Real.exp (2 * v - κ / 2 * v ^ 2)) atTop (𝓝 0) :=
    tendsto_exp_two_sub_sq (by positivity)
  have hmul : Tendsto (fun v : ℝ =>
      ((1 + a * (v ^ 2) ^ 9) * (b + c * v ^ 2) * Real.exp (-(κ / 2 * v ^ 2)))
        * Real.exp (2 * v - κ / 2 * v ^ 2)) atTop (𝓝 (0 * 0)) := hcomp.mul hrest
  rw [mul_zero] at hmul
  refine hmul.congr fun v => ?_
  have hexp : Real.exp (-(κ / 2 * v ^ 2)) * Real.exp (2 * v - κ / 2 * v ^ 2)
      = Real.exp (2 * v) * Real.exp (-(κ * v ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, hexp, ← mul_assoc]

end RHTower.Sieve
