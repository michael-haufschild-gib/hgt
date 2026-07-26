import GaloisForLFunctions.RHTower.UniformGaussianDominationOfTilts

/-!
# Zero margin forbids a single estimate and forces a vanishing-loss family

Two formulations of the hypothesis pin the same real number from opposite sides.  This file records
what that costs a method, and what it permits.

**The two instances.**  For the de Bruijn–Newman constant, `Λ ≥ 0` is a theorem and the hypothesis is
`Λ ≤ 0`, so the hypothesis is the *equality* `Λ = 0`.  For the moment sequence, log-convexity gives
`M_{j+1}²/(M_jM_{j+2}) ≤ 1` and the hypothesis gives the reverse up to a factor tending to one, so the
hypothesis is asymptotic equality.  These are the only two places in this development where a free
theorem and the hypothesis constrain the same scalar.

**What it forbids.**  A method that yields `Λ ≤ δ` for some fixed `δ > 0` yields nothing: the value
`δ/2` satisfies the free theorem and the estimate while violating the hypothesis.  No single estimate
with any positive loss can decide the question.

**What it permits.**  A *family* of estimates whose loss tends to zero does decide it: from `x ≤ f n`
for every `n` and `f n → 0` one gets `x ≤ 0`.  Zero margin does not forbid proof — it forbids proof by
one estimate and requires a one-parameter family with vanishing loss.

> **The correct shape of a proof in these formulations is a family of inequalities whose loss tends to
> zero, not a single inequality.  The order-two window is exactly such a family, with the shift as its
> parameter, which is why that case is provable; the higher orders fail not because no estimate exists
> but because the loss does not vanish.**

This file formalizes the pinch, the insufficiency of any fixed positive loss, the sufficiency of a
vanishing-loss family, and the fact that the order-two window width is such a family.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The pinch.**  Two opposing bounds on one scalar make the hypothesis an equality. -/
theorem zero_margin_pinch {x : ℝ} : (0 ≤ x ∧ x ≤ 0) ↔ x = 0 := by
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩

/-- **A fixed positive loss decides nothing.**  For any `δ > 0` there is a value satisfying the free
theorem and the estimate yet violating the hypothesis. -/
theorem single_estimate_insufficient {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ δ ∧ ¬ x ≤ 0 := by
  refine ⟨δ / 2, by linarith, by linarith, by intro h; linarith⟩

/-- **A vanishing-loss family decides it.**  From `x ≤ f n` for every `n` and `f n → 0` one gets
`x ≤ 0`. -/
theorem vanishing_loss_suffices {x : ℝ} {f : ℕ → ℝ}
    (hbound : ∀ n, x ≤ f n) (hlim : Tendsto f atTop (𝓝 0)) : x ≤ 0 :=
  ge_of_tendsto hlim (Eventually.of_forall hbound)

/-- And then the pinch closes: with the free lower bound, the value is exactly zero. -/
theorem vanishing_loss_gives_equality {x : ℝ} {f : ℕ → ℝ}
    (hfree : 0 ≤ x) (hbound : ∀ n, x ≤ f n) (hlim : Tendsto f atTop (𝓝 0)) : x = 0 :=
  zero_margin_pinch.mp ⟨hfree, vanishing_loss_suffices hbound hlim⟩

/-- **The order-two window is such a family.**  Its width `4(1 - windowRatio(2j))` tends to zero. -/
theorem window_width_tendsto_zero :
    Tendsto (fun j : ℕ => 4 * (1 - windowRatio (2 * j))) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => by omega) (fun b => ⟨b, by omega⟩)
  have h : Tendsto (fun j : ℕ => windowRatio (2 * j)) atTop (𝓝 1) :=
    windowRatio_tendsto_one.comp hcomp
  have hsub : Tendsto (fun j : ℕ => 1 - windowRatio (2 * j)) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h
  rw [show (1 : ℝ) - 1 = 0 by norm_num] at hsub
  simpa using hsub.const_mul (4 : ℝ)

/-- So the order-two case has the right shape: a free bound, a family of estimates, and a loss that
vanishes in the parameter. -/
theorem order_two_has_the_right_shape {x : ℝ} (hfree : 0 ≤ x)
    (hbound : ∀ j : ℕ, x ≤ 4 * (1 - windowRatio (2 * j))) : x = 0 :=
  vanishing_loss_gives_equality hfree hbound window_width_tendsto_zero

end RHTower
