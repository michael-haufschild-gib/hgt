import GaloisForLFunctions.RHTower.FamiliesDoNotChangeTheExponent

/-!
# Only a vertical parameter can carry a vanishing loss

Every closed lane in this development was closed by a count in which budget and demand scale the same
way.  This file isolates why that is fatal and which parameters escape it.

**Equal weights give a constant loss.**  If a tool's budget is `c_B (log T)^w` and its demand is
`c_D (log T)^w` — the same power — then the loss is the constant `c_B/c_D` at every height.  By the
zero-margin entry, a constant loss decides nothing.

**Unequal weights give a vanishing loss.**  If the budget's weight is strictly smaller, the ratio
tends to zero and the limiting argument closes.

**Which parameters have unequal weights.**  Height-indexed tools do not: degrees of freedom, zero
density and prime cost all carry the same power of `log T`, which is the content of the exchange-rate
entries.  The parameters that can differ are the *vertical* ones — the jet order at the centre, the
minor order, the derivative order, and the heat-flow time.  Of these:

* jet order gives a vanishing loss at order two and only there;
* minor order fails from order three by the Vandermonde exponent;
* derivative order is disjoint from an equivalent subfamily;
* **heat-flow time** is the one where the question is open: the known upper bounds on the flow
  constant form a decreasing sequence not proved to tend to zero, which is exactly a non-vanishing
  loss.

> **Height-indexed tools are equivariant and therefore have a constant loss, which by the zero-margin
> entry can never decide the question.  Only a vertical parameter can carry a vanishing loss, and of
> the four vertical parameters the flow time is the only one whose vanishing-loss question is open.**

This file formalizes the constancy of the loss at equal weights, its vanishing at unequal weights, and
the insufficiency of a bounded-away-from-zero family of upper bounds.
-/

open Filter Topology Real

noncomputable section

namespace RHTower

/-- **Equal weights give a constant loss.**  The ratio of two quantities with the same power is the
ratio of their constants, independent of the height. -/
theorem equal_weight_constant_loss {cB cD w x : ℝ} (hcD : cD ≠ 0) (hx : 0 < x) :
    (cB * x ^ w) / (cD * x ^ w) = cB / cD := by
  have hpow : x ^ w ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx w)
  field_simp

/-- **Unequal weights give a vanishing loss.**  A strictly smaller weight on the budget sends the
ratio to zero. -/
theorem lower_weight_vanishing {cB cD wB wD : ℝ} (hw : wB < wD) :
    Tendsto (fun x : ℝ => (cB / cD) * x ^ (wB - wD)) atTop (𝓝 0) := by
  have hneg : Tendsto (fun x : ℝ => x ^ (wB - wD)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x ^ (-(wD - wB))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    simpa [neg_sub, sub_eq_add_neg] using this
  simpa using hneg.const_mul (cB / cD)

/-- The two regimes are exclusive: with equal weights the loss is a fixed constant, which is the
hypothesis of the zero-margin obstruction. -/
theorem constant_loss_is_fixed {cB cD : ℝ} (hcD : cD ≠ 0) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (w : ℝ) :
    (cB * x ^ w) / (cD * x ^ w) = (cB * y ^ w) / (cD * y ^ w) := by
  rw [equal_weight_constant_loss hcD hx, equal_weight_constant_loss hcD hy]

/-- **A family of upper bounds bounded away from zero decides nothing.**  If every bound exceeds a
fixed positive number, a positive value satisfies them all. -/
theorem bounded_family_insufficient {f : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (hf : ∀ n, ε ≤ f n) :
    ∃ x : ℝ, 0 ≤ x ∧ (∀ n, x ≤ f n) ∧ ¬ x ≤ 0 := by
  refine ⟨ε / 2, by linarith, fun n => by linarith [hf n], by intro h; linarith⟩

/-- **And a family tending to zero does decide it**, which is the shape a flow-time argument would
need. -/
theorem vanishing_family_decides {x : ℝ} {f : ℕ → ℝ} (hfree : 0 ≤ x)
    (hf : ∀ n, x ≤ f n) (hlim : Tendsto f atTop (𝓝 0)) : x = 0 :=
  vanishing_loss_gives_equality hfree hf hlim

/-- The known situation for the flow constant: decreasing bounds with a positive infimum are exactly
the insufficient case. -/
theorem decreasing_bounds_not_enough {f : ℕ → ℝ} (_hanti : Antitone f) {ε : ℝ} (hε : 0 < ε)
    (hinf : ∀ n, ε ≤ f n) :
    ∃ x : ℝ, 0 ≤ x ∧ (∀ n, x ≤ f n) ∧ ¬ x ≤ 0 :=
  bounded_family_insufficient hε hinf

end RHTower
