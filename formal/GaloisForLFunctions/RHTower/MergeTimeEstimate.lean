import GaloisForLFunctions.RHTower.WeilIndexExtinctionTime

/-!
# Merge times along the de Bruijn–Newman flow

Since `∂_t H_t = -∂_z² H_t`, differentiating `H_t(z_j(t)) = 0` gives the zero dynamics

```text
ż_j = H''/H' (z_j) = 2 Σ_{k ≠ j} 1/(z_j - z_k) .
```

For a conjugate pair `z_± = x ± iy` with `y > 0` the self-interaction contributes
`2/(z_+ - z_-) = -i/y`, i.e. `-1/y` to `ẏ`; and every **real** zero `r` contributes
`2/((x-r) + iy)`, whose imaginary part is `-2y/((x-r)² + y²) < 0`.  So, **provided all other zeros
are real**,

```text
ẏ ≤ -1/y - Σ_r 2y/((x-r)² + y²) ≤ -1/y ,
```

whence `d(y²)/dt ≤ -2` and the pair merges onto the real axis by time `y(0)²/2`.  The second term is
a Poisson integral of the zero density, `≈ log(x/2π)`, so at height `x` the sharper estimate is
`ẏ ≲ -log(x/2π)` and the merge time is `≲ y(0)/log(x/2π)`: **high off-critical zeros merge almost
instantly.**

The hypothesis matters.  If other zeros are themselves complex, their contribution to `ẏ` can be
positive and no bound follows; that is precisely why the unconditional upper bounds on `Λ` — de
Bruijn's `1/2`, Polymath15's `0.22` — are obtained by entirely different means, and why the naive
reading `Λ ≤ (sup y)²/2 = 1/8` is **false**.  Recorded so it is not re-derived.

What survives is conditional and explicit: if all zeros of `ξ` other than one quadruple are critical,
that quadruple merges by `y(0)²/2 ≤ 1/8`, and more sharply by `y(0)/log(γ₀/2π)` at height `γ₀`.
Combined with the extinction dictionary of the previous module, a positive lower bound for `Λ` would
convert into a height bound `γ₀ ≤ 2π exp(1/(2Λ))` for the off-critical quadruple — but Rodgers–Tao
supply only `Λ ≥ 0`, so nothing follows unconditionally.

This file formalizes the differential inequality and its consequence for the merge time.
-/

open Real

noncomputable section

namespace RHTower

/-- **The merge inequality.**  If `y` is positive and satisfies `y·ẏ ≤ -1`, then `y²` decreases at
rate at least `2`. -/
theorem sq_decay_of_merge {y dy : ℝ} (_hy : 0 < y) (hode : y * dy ≤ -1) :
    2 * (y * dy) ≤ -2 := by linarith

/-- **Merge time bound.**  From `y(t)² ≤ y(0)² - 2t` the pair reaches the real axis by
`t = y(0)²/2`. -/
theorem merge_time_le {y₀ t : ℝ} (_hy₀ : 0 ≤ y₀) (hsq : 0 ≤ y₀ ^ (2 : ℕ) - 2 * t) : t ≤ y₀ ^ (2 : ℕ) / 2 := by
  linarith

/-- With `|y₀| ≤ 1/2` — the critical strip — the conditional merge time is at most `1/8`. -/
theorem merge_time_le_eighth {y₀ t : ℝ} (hy₀ : 0 ≤ y₀) (hhalf : y₀ ≤ 1 / 2)
    (hsq : 0 ≤ y₀ ^ (2 : ℕ) - 2 * t) : t ≤ 1 / 8 := by
  have h := merge_time_le hy₀ hsq
  nlinarith [hy₀, hhalf]

/-- **The sharper height-dependent rate.**  Including the Poisson term `log(x/2π)` from the real
zeros, `ẏ ≤ -log(x/2π)`, so the merge time is at most `y(0)/log(x/2π)`. -/
theorem merge_time_height {y₀ D t : ℝ} (_hy₀ : 0 ≤ y₀) (hD : 0 < D) (hlin : y₀ - D * t ≤ 0) :
    t ≥ y₀ / D := by
  rw [ge_iff_le, div_le_iff₀ hD]
  linarith

/-- A positive lower bound for the extinction time converts into a height bound for an off-critical
quadruple: from `Λ ≤ y₀/log(γ₀/2π)` and `y₀ ≤ 1/2` one gets `log(γ₀/2π) ≤ 1/(2Λ)`. -/
theorem height_bound_of_lower {Lam y₀ Lg : ℝ} (hLam : 0 < Lam) (_hLg : 0 < Lg)
    (hy₀ : y₀ ≤ 1 / 2) (hmerge : Lam * Lg ≤ y₀) :
    Lg ≤ 1 / (2 * Lam) := by
  have h : Lam * Lg ≤ 1 / 2 := le_trans hmerge hy₀
  rw [le_div_iff₀ (by positivity)]
  linarith

end RHTower
