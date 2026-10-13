import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A two-window certificate beyond bandwidth one

In the pair-correlation model of the rank–trace certificate, a window density `ψ ≥ 0` with `∫ψ = 1`
certifies the proportion `2 − Q(ψ)`, where

`Q(ψ) = ∫ψ² + E f(|X − Y|)`,  `X, Y` independent with density `ψ`,

`f(u) = u` for `u ≤ 1` (Montgomery) and `f(u) = B` for `u > 1` (the assumed bound for the
pair-correlation form factor beyond one).  The uniform density on an interval of length `4/3` gives
`Q = 9/8 + B/16`, i.e. exactly `3/4` at `B = 2` (`PairCorrelationExchangeRate`).

The uniform density is not optimal.  Mixing it with the uniform density on an interval of length `1`,

`ψ_ε = (1 − ε)·U[−2/3, 2/3] + ε·U[−1/2, 1/2]`,

the form is the quadratic `(1−ε)² Q_s + 2ε(1−ε) Q_× + ε² Q₁` with `Q_s = 9/8 + B/16`, `Q₁ = 4/3` and
cross term `Q_× = 3/4 + E f(|X − Y|) = 971/864 + B/48` (`cross_density_integral`: the density of `X − Y` is
the trapezoid of plateau `3/4` on `|d| ≤ 1/6` vanishing at `|d| = 7/6`).  Then (`mixture_beats_uniform`,
`mixture_three_quarters`):

* at `B = 2` the mixture with `ε = 1/3` certifies more than `3/4` (in fact `≈ 0.778`);
* three quarters survives up to `B = 14/5` (with `ε = 7/16`).

So, for this certificate, three quarters needs only `F ≤ 14/5` on `(1, 4/3)` instead of `F ≤ 2`.
-/

open intervalIntegral

noncomputable section

namespace RHTower

/-- **The cross term**: `E f(|X − Y|) = 2 ∫₀^{7/6} trap(d) f(d) dd = 323/864 + B/48`. -/
theorem cross_density_integral (B : ℝ) :
    2 * ((∫ d in (0:ℝ)..(1 / 6), 3 / 4 * d) + (∫ d in (1 / 6 : ℝ)..1, 3 / 4 * (7 / 6 - d) * d)
      + ∫ d in (1:ℝ)..(7 / 6), 3 / 4 * (7 / 6 - d) * B) = 323 / 864 + B / 48 := by
  have h1 : ∫ d in (0:ℝ)..(1 / 6), 3 / 4 * d = 1 / 96 := by
    rw [integral_const_mul, integral_id]; norm_num
  have h2 : ∫ d in (1 / 6 : ℝ)..1, 3 / 4 * (7 / 6 - d) * d = 305 / 1728 := by
    have e : (fun d : ℝ => 3 / 4 * (7 / 6 - d) * d) = fun d => 7 / 8 * d - 3 / 4 * d ^ 2 := by
      funext d; ring
    rw [e, integral_sub ((by fun_prop : Continuous fun d : ℝ => 7 / 8 * d).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun d : ℝ => 3 / 4 * d ^ 2).intervalIntegrable _ _),
      integral_const_mul, integral_const_mul, integral_id, integral_pow]
    norm_num
  have h3 : ∫ d in (1:ℝ)..(7 / 6), 3 / 4 * (7 / 6 - d) * B = B / 96 := by
    have e : (fun d : ℝ => 3 / 4 * (7 / 6 - d) * B) = fun d => 7 / 8 * B - 3 / 4 * B * d := by
      funext d; ring
    rw [e, integral_sub ((by fun_prop : Continuous fun _ : ℝ => 7 / 8 * B).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun d : ℝ => 3 / 4 * B * d).intervalIntegrable _ _),
      integral_const, integral_const_mul, integral_id]
    simp only [smul_eq_mul]; ring
  rw [h1, h2, h3]; ring

/-- The pair-correlation form of the mixture `ψ_ε`. -/
def mixQ (B ε : ℝ) : ℝ :=
  (1 - ε) ^ 2 * (9 / 8 + B / 16) + 2 * ε * (1 - ε) * (971 / 864 + B / 48) + ε ^ 2 * (4 / 3)

/-- The uniform window is the case `ε = 0`. -/
theorem mixQ_zero (B : ℝ) : mixQ B 0 = 9 / 8 + B / 16 := by unfold mixQ; ring

/-- **The mixture beats the uniform window at `B = 2`.** -/
theorem mixture_beats_uniform : 3 / 4 < 2 - mixQ 2 (1 / 3) := by
  unfold mixQ; norm_num

/-- **Three quarters with `F ≤ 14/5` beyond one.** -/
theorem mixture_three_quarters {B : ℝ} (hB : B ≤ 14 / 5) : 3 / 4 ≤ 2 - mixQ B (7 / 16) := by
  unfold mixQ; nlinarith

end RHTower
