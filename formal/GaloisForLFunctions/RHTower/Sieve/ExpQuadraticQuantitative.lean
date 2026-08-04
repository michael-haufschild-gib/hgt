import GaloisForLFunctions.RHTower.Sieve.ExpQuadraticDecay

/-!
# The quadratic beats the linear, with an explicit threshold

`ExpQuadraticDecay` shows `exp(2v - κv²) → 0`, and uses it only qualitatively.  The comparison is in
fact explicit: as soon as `v ≥ 4/κ` the linear term is at most half the quadratic one, so

    exp(2v - κv²) ≤ exp(-κv²/2) .

With `v = (log N)^{1/20}` and `κ = c₀/8192` this is the saving of the contour argument surviving the
price of narrow smoothing, with a rate rather than as an `o(1)`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The linear term is at most half the quadratic one past an explicit threshold.** -/
theorem two_mul_le_half_sq {κ v : ℝ} (hκ : 0 < κ) (hv : 4 / κ ≤ v) :
    2 * v ≤ κ * v ^ 2 / 2 := by
  have h4 : (0 : ℝ) < 4 / κ := by positivity
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le h4 hv
  have hκv : (4 : ℝ) ≤ κ * v := by
    rw [div_le_iff₀ hκ] at hv
    linarith
  nlinarith [hκv, hv0]

/-- **The quadratic decay, with an explicit threshold.** -/
theorem exp_two_sub_sq_le {κ v : ℝ} (hκ : 0 < κ) (hv : 4 / κ ≤ v) :
    Real.exp (2 * v - κ * v ^ 2) ≤ Real.exp (-(κ * v ^ 2 / 2)) := by
  refine Real.exp_le_exp.2 ?_
  have := two_mul_le_half_sq hκ hv
  linarith

/-- The same, as an eventual statement. -/
theorem eventually_exp_two_sub_sq_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ v : ℝ in atTop, Real.exp (2 * v - κ * v ^ 2) ≤ Real.exp (-(κ * v ^ 2 / 2)) := by
  filter_upwards [eventually_ge_atTop (4 / κ)] with v hv
  exact exp_two_sub_sq_le hκ hv

end RHTower.Sieve
