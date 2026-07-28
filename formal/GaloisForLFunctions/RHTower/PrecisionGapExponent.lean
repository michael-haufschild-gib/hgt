import Mathlib

/-!
# The crossing of `X^{-θ}` against `log X / √X`

Comparisons in analytic number theory frequently reduce to whether a saving of the form
`error ≪ X^{1−θ}` on a quantity of size `X` supplies enough relative precision to decide a
comparison whose margin is of relative size `log X / √X`.  The two sides cross at exactly
`θ = 1/2`: for `θ > 1/2` the saving eventually suffices, for `θ < 1/2` it eventually fails.

This file formalizes that crossing as pure real analysis.  It carries no claim about any particular
number-theoretic functional; an earlier version of this file asserted such an application to the
rectangular Weil carrier, and that assertion was withdrawn — see the note below.

**Withdrawn application.**  The rectangular criterion of
`SuzukiRectangularPositiveArchLagCompletion` fixes the window width `L` and lets the aperture
`a = ½log n` grow, with the prime sum running to `⌊e^{2a}⌋ = n`.  The autocorrelation's four-tent
expansion

```text
R(L,a,h) = 2·max(0, L−|h|) + max(0, L−|h−(2a−L)|) + max(0, L−|h+(2a−L)|)
```

is compactly supported in `h`, so the prime side splits into a fixed small-prime tent — constant in
`a` — and a moving window at `log k ≈ 2a`, whose mass is of order `√n`.  The archimedean budget is
of the *same* order, not polynomial against an exponential.  Both sides therefore grow together and
the criterion compares lower-order terms; the crossing below does not apply to it.
-/

open Filter Topology Asymptotics Real

namespace RHTower

/-- **The required relative precision.**  Budget over mass tends to zero at rate `log X / √X`. -/
theorem precision_demand_tendsto_zero :
    Tendsto (fun X : ℝ => Real.log X / Real.sqrt X) atTop (nhds 0) := by
  have h := isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)
  refine h.tendsto_div_nhds_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X _
  rw [Real.sqrt_eq_rpow]

/-- **A supercritical saving eventually suffices.**  For `θ > 1/2` the relative precision `X^{−θ}`
is eventually finer than the demand `log X / √X`, because `X^{1/2−θ}` tends to zero while the
logarithm diverges. -/
theorem supercritical_saving_suffices {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∀ᶠ X in atTop, X ^ (-θ) < Real.log X / Real.sqrt X := by
  have hneg : Tendsto (fun X : ℝ => X ^ (-(θ - 1 / 2))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  filter_upwards [hneg.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually_gt_atTop 1, eventually_gt_atTop (1 : ℝ)] with X h1 h2 h3
  have hXpos : (0 : ℝ) < X := lt_trans one_pos h3
  rw [Real.sqrt_eq_rpow, lt_div_iff₀ (Real.rpow_pos_of_pos hXpos _), ← Real.rpow_add hXpos,
    show -θ + 1 / 2 = -(θ - 1 / 2) by ring]
  linarith

/-- **A subcritical saving eventually fails.**  For `0 < θ < 1/2` the relative precision `X^{−θ}` is
eventually coarser than the demand, so no such saving decides the comparison at large windows. -/
theorem subcritical_saving_fails {θ : ℝ} (_hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ᶠ X in atTop, Real.log X / Real.sqrt X < X ^ (-θ) := by
  have h := isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2 - θ) (by linarith)
  have hdiv : Tendsto (fun X : ℝ => Real.log X / X ^ ((1 : ℝ) / 2 - θ)) atTop (nhds 0) :=
    h.tendsto_div_nhds_zero
  filter_upwards [hdiv.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with X h1 h2
  have hXpos : (0 : ℝ) < X := lt_trans one_pos h2
  have hkey : Real.log X < X ^ ((1 : ℝ) / 2 - θ) := by
    rwa [div_lt_one (Real.rpow_pos_of_pos hXpos _)] at h1
  rw [Real.sqrt_eq_rpow, div_lt_iff₀ (Real.rpow_pos_of_pos hXpos _), ← Real.rpow_add hXpos,
    show -θ + 1 / 2 = (1 : ℝ) / 2 - θ by ring]
  exact hkey

/-- **The wall is at exactly one half.**  Supercritical savings eventually suffice and subcritical
savings eventually fail, so the deciding exponent is `1/2` — the square root of the prime-number
theorem error term, which is the hypothesis itself. -/
theorem precision_wall_at_one_half {θ₁ θ₂ : ℝ} (h1 : 1 / 2 < θ₁) (h2 : 0 < θ₂) (h3 : θ₂ < 1 / 2) :
    (∀ᶠ X in atTop, X ^ (-θ₁) < Real.log X / Real.sqrt X) ∧
      (∀ᶠ X in atTop, Real.log X / Real.sqrt X < X ^ (-θ₂)) :=
  ⟨supercritical_saving_suffices h1, subcritical_saving_fails h2 h3⟩

end RHTower
