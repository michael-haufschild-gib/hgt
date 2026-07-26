import GaloisForLFunctions.RHTower.ZeroMarginForcesALimitingArgument

/-!
# Three types of approach, and a root cause for each

Applying the previous entry's criterion to Li's coefficients separates the subject into three
profiles.  This file computes the Li profile and records the classification.

**The Li profile.**  Li's criterion is `λ_n ≥ 0` for all `n`, with

```text
λ_n  =  (n/2) log n  +  c n  +  (arithmetic term) .
```

Its margin is the archimedean main term `(n/2) log n`, which **grows without bound** — the opposite of
the zero-margin profile.  Its falsification signal is also amplified: an off-line zero `ρ = β + iγ`
gives `|1 - 1/ρ| > 1` exactly when `β < 1/2`, since

```text
|1 - 1/ρ|²  =  ((β-1)² + γ²) / (β² + γ²)  >  1   ⟺   β < ½ ,
```

and the functional equation pairs `ρ` with `1 - ρ`, so any off-line zero produces one of each.  A
counterexample therefore drives `λ_n` by an **exponentially growing** term.

**So why is it open?**  Because the arithmetic term is not controlled unconditionally by anything
smaller than the main term.  Li's criterion trades zero margin for unbounded error.

> **Every approach in this development falls into one of three types.  Type A: the margin is zero and
> the error is controlled — only a family with vanishing loss can work.  Type B: the margin grows but
> the error is uncontrolled — only error control can work.  Type C: margin and error measure different
> quantities — no comparison is possible at all.**

This file formalizes the off-line amplification criterion, the growth of the Li margin, and the two
logical shapes that types A and B require.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The amplification criterion.**  For a zero at `β + iγ` the multiplier `|1 - 1/ρ|` exceeds one
exactly when `β < 1/2`. -/
theorem amplification_iff {β γ : ℝ} (hden : 0 < β ^ 2 + γ ^ 2) :
    ((β - 1) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2) > 1 ↔ β < 1 / 2 := by
  rw [gt_iff_lt, lt_div_iff₀ hden, one_mul]
  constructor <;> intro h <;> nlinarith

/-- **The functional equation supplies an amplifying partner.**  If a zero is off the critical line,
then either it or its reflection has real part below one half. -/
theorem reflection_gives_amplifier {β : ℝ} (h : β ≠ 1 / 2) :
    β < 1 / 2 ∨ 1 - β < 1 / 2 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr (by linarith)

/-- **Amplification is exponential.**  A multiplier above one drives the powers to infinity. -/
theorem amplifier_tendsto_atTop {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt hr

/-- **The Li margin grows.**  The archimedean main term `(n/2) log n` tends to infinity, so the
profile is the opposite of zero margin. -/
theorem li_margin_tendsto_atTop :
    Tendsto (fun n : ℕ => ((n : ℝ) / 2) * Real.log n) atTop atTop := by
  have hhalf : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hhalf.atTop_mul_atTop₀ hlog

/-- **The type-B shape.**  With a growing main term and an error, nonnegativity follows exactly when
the error does not exceed the main term. -/
theorem typeB_shape {x M E : ℝ} (hlower : M - E ≤ x) (herr : E ≤ M) : 0 ≤ x := by
  linarith

/-- And a relative error tending to zero eventually gives that. -/
theorem typeB_relative {M E : ℝ} (hM : 0 < M) (hrel : E / M ≤ 1) : E ≤ M := by
  rwa [div_le_one hM] at hrel

/-- **The type-A shape**, restated for comparison: with zero margin only a vanishing-loss family
works, and a fixed positive loss never does. -/
theorem typeA_shape {x : ℝ} {f : ℕ → ℝ}
    (hfree : 0 ≤ x) (hbound : ∀ n, x ≤ f n) (hlim : Tendsto f atTop (𝓝 0)) : x = 0 :=
  vanishing_loss_gives_equality hfree hbound hlim

/-- **The two types are genuinely different.**  A type-B situation is decided by a single estimate on
the error, which the previous entry showed is impossible for type A. -/
theorem typeB_single_estimate_suffices {x M E : ℝ} (hlower : M - E ≤ x)
    (herr : E ≤ M) : 0 ≤ x :=
  typeB_shape hlower herr

end RHTower
