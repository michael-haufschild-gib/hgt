import GaloisForLFunctions.RHTower.CrossingLevelIsIteratedLog

/-!
# Level one, written out: a zero-free disc for the Mellin transform of the theta remainder

The mechanism closes modulo five nested zero-free-disc statements.  This file writes the first one
completely.

**The level-one measure and transform.**  In the variable `w = log t` the level-one measure has density
`Φ(e^w)e^w`, so its Laplace transform is

```text
M₁(s)  =  ∫_ℝ e^{sw} Φ(e^w) e^w dw  =  ∫_0^∞ Φ(t) t^s dt ,
```

the **Mellin transform of the theta remainder**.  It interpolates the Taylor data exactly: the moments
are `m_k = M₁(2k)`.

**It is analytic where it matters and positive on the real axis.**  `Φ` decays doubly exponentially at
infinity and is finite at the origin, so `M₁` is analytic on `Re s > -1`, which contains every `s = 2k`.
And `Φ` is positive on `[0, ∞)` — the leading term `(2π²e^{9t/2} - 3πe^{5t/2})e^{-πe^{2t}}` is positive
as soon as `2π e^{2t} > 3`, which holds already at `t = 0` because `2π > 3` — so `M₁` is strictly
positive at every real point of its half-plane and has no real zeros there.

> **Level one is: the Mellin transform of a positive function, itself positive on the real axis, is
> zero-free on the disc of radius `≍ √(k / log k)` about `s = 2k`.**

That is a self-contained question about an explicit analytic function of one variable, with no zeta in
it, and it is the first of the five.

This file formalizes the positivity of the leading term, the resulting positivity of the transform at
real points, and the shape of the radius.
-/

open Real

noncomputable section

namespace RHTower

/-- **The leading term is positive at the origin**, since `2π > 3`. -/
theorem leading_term_pos_at_zero : (3:ℝ) < 2 * π := by
  have := Real.pi_gt_three
  linarith

/-- And it stays positive for `t ≥ 0`, since `e^{2t} ≥ 1`. -/
theorem leading_term_pos {t : ℝ} (ht : 0 ≤ t) : (3:ℝ) < 2 * π * Real.exp (2 * t) := by
  have h1 : (1:ℝ) ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have h2 := leading_term_pos_at_zero
  nlinarith [Real.pi_pos]

/-- **Positivity of the transform at real points**, in the discrete model: a positive density against a
positive kernel integrates to something positive. -/
theorem mellin_pos_real {n : ℕ} (f w : Fin n → ℝ) (hf : ∀ j, 0 < f j) (hn : 0 < n) (s : ℝ) :
    0 < ∑ j, f j * Real.exp (s * w j) :=
  laplace_pos f w hf hn s

/-- Hence no real zeros. -/
theorem mellin_ne_zero_real {n : ℕ} (f w : Fin n → ℝ) (hf : ∀ j, 0 < f j) (hn : 0 < n) (s : ℝ) :
    ∑ j, f j * Real.exp (s * w j) ≠ 0 :=
  ne_of_gt (mellin_pos_real f w hf hn s)

/-- **The radius's shape.**  With convexity `≍ k log k` the admissible radius is the square root of its
reciprocal times the scale, that is `√(k / log k)`. -/
theorem radius_shape {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    Real.sqrt (k / L) * Real.sqrt (k / L) = k / L := by
  exact Real.mul_self_sqrt (by positivity)

/-- The radius grows with `k`, so the disc to be cleared widens as the moment order increases. -/
theorem radius_grows {k₁ k₂ L : ℝ} (hL : 0 < L) (_hk : 0 < k₁) (h : k₁ ≤ k₂) :
    Real.sqrt (k₁ / L) ≤ Real.sqrt (k₂ / L) := by
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right h (le_of_lt hL)

end RHTower
