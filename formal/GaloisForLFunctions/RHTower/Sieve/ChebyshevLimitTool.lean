import GaloisForLFunctions.RHTower.Sieve.SqrtExpDecay
import GaloisForLFunctions.RHTower.Sieve.ChebyshevWidth

/-!
# The one limit every error term reduces to

Each term of the contour bound, divided by the cutoff, is at most a constant times

    t^n · exp(2(log x)^{1/20}) · exp(-κ(log x)^{1/10}),   t = (log x)^{1/10},

with `κ > 0`.  Since `(log x)^{1/20} = √t`, this is the square-root-against-linear estimate composed
with `t(x) → ∞`.

Everything after this point is bookkeeping: identify `n` and `κ` for each term and apply.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The height's exponent grows without bound. -/
theorem tendsto_logRoot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop

/-- **The master limit.**  A power of `t`, the width's square-root growth, and the contour's saving. -/
theorem tendsto_logPoly_sqrt_saving (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => ((Real.log x) ^ ((1 : ℝ) / 10)) ^ n
        * Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 20))
        * Real.exp (-(κ * (Real.log x) ^ ((1 : ℝ) / 10)))) atTop (𝓝 0) := by
  have hcomp := (tendsto_poly_sqrt_exp_neg n hκ).comp tendsto_logRoot
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp_apply]
  rw [sqrt_logRoot hL]

/-- The saving alone, without a polynomial factor. -/
theorem tendsto_sqrt_saving {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 20))
        * Real.exp (-(κ * (Real.log x) ^ ((1 : ℝ) / 10)))) atTop (𝓝 0) := by
  have h := tendsto_logPoly_sqrt_saving 0 hκ
  refine h.congr fun x => ?_
  rw [pow_zero, one_mul]

end RHTower.Sieve
