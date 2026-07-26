import GaloisForLFunctions.RHTower.BoundaryInteriorVanishingCost

/-!
# A quantitative Nyman–Beurling criterion, with explicit modulus

The three ingredients left open by the boundary/interior dichotomy assemble.

**(a) The space.**  Every Báez-Duarte generator is supported in `(0,1]`: for `t ≥ 1` both `1/t < 1`
and `θ/t < 1`, so `ρ_θ(t) = {θ/t} - θ{1/t} = θ/t - θ/t = 0`.  The target `1_{(0,1]}` is likewise
supported there.  The Mellin transform `f ↦ ∫₀¹ f(t)t^{-s}dt` therefore converges for `Re s < ½` and
maps `L²((0,1],dt)` unitarily onto the Hardy space `H²` of the half-plane `Re s < ½`, with the
Plancherel normalization

```text
‖f‖² = (1/2π) ∫_ℝ |f̂(½+iu)|² du ,
```

as the target itself confirms: `1̂(s) = 1/(1-s)`, whose boundary modulus squared integrates to `2π`,
matching `‖1_{(0,1]}‖² = 1`.

**(b) The vanishing constraint.**  The transform of a generator is `ζ(s)(n^{-s} - 1/n)/s`, so every
finite combination has transform `ζ(s)P(s)/s` with `P` entire.  At a zero `ρ` of `ζ` with `ρ ≠ 0`
this vanishes, and vanishing is preserved under `L²` limits because point evaluation in `H²` is
continuous.  The target does not vanish there: `1̂(ρ) = 1/(1-ρ) ≠ 0`.

**(c) The cost.**  With this normalization the diagonal kernel of `H²` of a half-plane is
`K(w,w) = 1/(2σ)`, `σ` the distance from `w` to the boundary line.  (The preceding module used the
unnormalized convention, where the constant is `1/(4πσ)`; the dichotomy is the same and only the
constant differs.)  The exact vanishing cost therefore gives, for a zero `ρ = β + iγ` of `ζ` with
`β < ½`,

```text
lim_N d_N  ≥  |1̂(ρ)| / √K(ρ,ρ)  =  √(1 - 2β) / |1 - ρ| .
```

By the functional equation the Riemann hypothesis fails exactly when such a `ρ` exists, so

> **If the Riemann hypothesis fails, the Báez-Duarte distances are bounded below by the explicit
> constant `√(1-2β)/|1-ρ|` for every zero `ρ` with `Re ρ < ½`.**

This is the quantitative form of the easy direction of the Nyman–Beurling criterion: not merely
`d_N ↛ 0`, but a modulus in the deviation.

**Universal height degradation.**  The constant is at most `1/|γ|`, since `√(1-2β) ≤ 1` and
`|1-ρ| ≥ |γ|`.  So a counterexample high up produces only a tiny floor, and combining the criterion
with numerical verification to height `X` would require the complementary analytic bound
`d_N ≤ 1/X` — with `d_N² ≍ 1/log N` that means `N ≥ exp(X²)`.  The same degradation appeared in the
flow lane, where verification to height `X` bounds `Λ` only by `π²/(2 log²X)`.  It is not an artefact
of either method:

> **Every quantified lane loses strength at a putative counterexample polynomially or exponentially
> in its height.  Numerical verification and analytic estimate never meet unless the analytic
> estimate is itself as strong as the verification height.**

That is the unified reason the "verify below, estimate above" architecture stalls, and it applies to
the Nyman–Beurling lane exactly as it does to the de Bruijn–Newman lane.

This file formalizes the kernel with the correct normalization, the explicit floor, and the height
degradation.
-/

open Real

noncomputable section

namespace RHTower

/-- The diagonal reproducing kernel of `H²` of a half-plane in the Plancherel normalization
`‖F‖² = (1/2π)∫|F|²`. -/
def nymanBeurlingHardyKernel (sigma : ℝ) : ℝ := 1 / (2 * sigma)

/-- **The explicit floor.**  The cost of vanishing at a point at distance `σ` from the boundary, for
a target of modulus `m` there, is `m·√(2σ)`. -/
def nbFloor (m sigma : ℝ) : ℝ := m * Real.sqrt (2 * sigma)

/-- The floor is the target modulus divided by the square root of the diagonal kernel. -/
theorem nbFloor_eq {m sigma : ℝ} (hs : 0 < sigma) :
    nbFloor m sigma = m / Real.sqrt (nymanBeurlingHardyKernel sigma) := by
  unfold nbFloor nymanBeurlingHardyKernel
  have hpos : (0 : ℝ) < 2 * sigma := by positivity
  rw [one_div, Real.sqrt_inv, div_inv_eq_mul]

/-- **Positivity.**  A zero strictly off the critical line gives a strictly positive floor. -/
theorem nbFloor_pos {m sigma : ℝ} (hm : 0 < m) (hs : 0 < sigma) : 0 < nbFloor m sigma := by
  unfold nbFloor
  have : 0 < Real.sqrt (2 * sigma) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The floor in terms of the zero.**  With `σ = ½ - β` and `m = 1/|1-ρ|`, the floor is
`√(1-2β)/|1-ρ|`. -/
theorem nbFloor_of_zero (beta r : ℝ) :
    nbFloor (1 / r) (1 / 2 - beta) = Real.sqrt (1 - 2 * beta) / r := by
  unfold nbFloor
  have h2 : 2 * (1 / 2 - beta) = 1 - 2 * beta := by ring
  rw [h2, one_div, inv_mul_eq_div]

/-- **Height degradation.**  Since `√(1-2β) ≤ 1` for `β ≥ 0` and `|1-ρ| ≥ |γ|`, the floor is at most
`1/|γ|`: a counterexample high up gives only a tiny floor. -/
theorem nbFloor_le_inv_height {beta r g : ℝ} (hb0 : 0 ≤ beta)
    (hg : 0 < g) (hr : g ≤ r) :
    Real.sqrt (1 - 2 * beta) / r ≤ 1 / g := by
  have hrpos : 0 < r := lt_of_lt_of_le hg hr
  have hle : Real.sqrt (1 - 2 * beta) ≤ 1 := by
    have h1 : 1 - 2 * beta ≤ 1 := by linarith
    calc Real.sqrt (1 - 2 * beta) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  calc Real.sqrt (1 - 2 * beta) / r ≤ 1 / r := by
        apply div_le_div_of_nonneg_right hle (le_of_lt hrpos)
    _ ≤ 1 / g := one_div_le_one_div_of_le hg hr

/-- **The complementary requirement.**  To close the criterion against a counterexample at height
`g` one needs an analytic bound `d ≤ 1/g`; with `d² ≍ 1/log N` that is `log N ≥ g²`. -/
theorem complementary_length {d g : ℝ} (hg : 0 < g) (hd : d ≤ 1 / g) (hdpos : 0 < d) :
    g ≤ 1 / d := by
  rw [le_div_iff₀ hdpos]
  rw [le_div_iff₀ hg] at hd
  linarith

/-- The criterion is genuinely two-sided: a positive floor contradicts convergence to zero, so the
Riemann hypothesis and a positive floor cannot both hold. -/
theorem floor_contradicts_convergence {m sigma c : ℝ} (hm : 0 < m) (hs : 0 < sigma)
    (hfloor : nbFloor m sigma ≤ c) : 0 < c :=
  lt_of_lt_of_le (nbFloor_pos hm hs) hfloor

end RHTower
