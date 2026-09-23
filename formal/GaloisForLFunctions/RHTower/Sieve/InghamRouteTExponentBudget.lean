import GaloisForLFunctions.RHTower.Sieve.InghamGabrielExponent

/-!
# Route T power-loss budget in Ingham--Gabriel interpolation

The sharp critical-line fourth moment is stronger than Route T needs.  Suppose its bound is allowed
the power loss `T^δ`, so that the zeta fourth moment has height exponent `1 + δ`.  Equation (41),
together with the linear-height mollifier second moment, then gives the critical `4/3` error moment
height exponent `1 + δ/3`.  Gabriel interpolation multiplies the usual density exponent by this
factor.

At Route T's target `σ = 7/10` and right edge `β = 1 + ε`, the resulting exponent remains below
`7/10` exactly when

`δ < (1 - 90 ε) / (10 (3 + 10 ε))`.

In particular, at the limiting right edge the available fourth-moment power-loss budget is `1/30`,
and the concrete pair `ε = 1/1000`, `δ = 1/100` stays strictly inside the admissible region.  Thus
formalising a `T^(101/100)` fourth-moment bound is sufficient for the fixed short-interval handoff;
an asymptotic formula or a sharp `T log^(4 : ℕ) T` estimate is unnecessary.
-/

namespace RHTower.Sieve

/-- Gabriel height exponent after a zeta fourth-moment power loss `T^δ`. -/
noncomputable def inghamRouteTHeightExponent (δ ε : ℝ) : ℝ :=
  (1 + δ / 3) *
    inghamGabrielHeightExponent (7 / 10 : ℝ) (1 + ε)

/-- Exact admissible fourth-moment loss at right-edge displacement `ε`. -/
noncomputable def inghamRouteTZetaMomentLossBudget (ε : ℝ) : ℝ :=
  (1 - 90 * ε) / (10 * (3 + 10 * ε))

/-- Closed form of the Route T height exponent with both analytic losses visible. -/
theorem inghamRouteTHeightExponent_eq
    {δ ε : ℝ} (hε : 0 ≤ ε) :
    inghamRouteTHeightExponent δ ε =
      (3 + δ) * (3 / 10 + ε) / (13 / 10 + 3 * ε) := by
  have hhalf : 1 + ε ≠ (1 / 2 : ℝ) := by linarith
  rw [inghamRouteTHeightExponent, inghamGabrielHeightExponent_eq hhalf]
  rw [show 3 * (1 + ε) - (7 / 10 : ℝ) - 1 = 13 / 10 + 3 * ε by ring]
  have hden : 13 / 10 + 3 * ε ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- Exact phase boundary: this fourth-moment loss is sufficient precisely below the stated
budget. -/
theorem inghamRouteTHeightExponent_lt_seven_tenths_iff
    {δ ε : ℝ} (hε : 0 ≤ ε) :
    inghamRouteTHeightExponent δ ε < 7 / 10 ↔
      δ < inghamRouteTZetaMomentLossBudget ε := by
  rw [inghamRouteTHeightExponent_eq hε, inghamRouteTZetaMomentLossBudget]
  have hden : 0 < 13 / 10 + 3 * ε := by linarith
  have hbudgetDen : 0 < 10 * (3 + 10 * ε) := by positivity
  rw [div_lt_iff₀ hden, lt_div_iff₀ hbudgetDen]
  constructor <;> intro h <;> nlinarith

/-- At the limiting right edge, Route T permits any zeta fourth-moment loss below `1/30`. -/
theorem inghamRouteTZetaMomentLossBudget_zero :
    inghamRouteTZetaMomentLossBudget 0 = 1 / 30 := by
  unfold inghamRouteTZetaMomentLossBudget
  norm_num

/-- A concrete rational budget leaving room on both the right edge and fourth moment. -/
theorem inghamRouteTHeightExponent_one_hundredth_one_thousandth :
    inghamRouteTHeightExponent (1 / 100 : ℝ) (1 / 1000 : ℝ) < 7 / 10 := by
  rw [inghamRouteTHeightExponent_lt_seven_tenths_iff (by norm_num)]
  unfold inghamRouteTZetaMomentLossBudget
  norm_num

/-- The same concrete budget in direct closed form, useful for downstream exponent comparisons. -/
theorem inghamRouteTHeightExponent_one_hundredth_one_thousandth_eq :
    inghamRouteTHeightExponent (1 / 100 : ℝ) (1 / 1000 : ℝ) =
      90601 / 130300 := by
  rw [inghamRouteTHeightExponent_eq (by norm_num)]
  norm_num

end RHTower.Sieve
