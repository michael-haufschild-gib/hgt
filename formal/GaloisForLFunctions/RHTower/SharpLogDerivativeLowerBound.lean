import GaloisForLFunctions.RHTower.KroneckerTransferThreshold

/-!
# A sharp lower bound for the real part of the logarithmic derivative

For `σ > 1` the classical two-sided estimate for the prime symbol is
`|Re(-ζ'/ζ(σ+it))| ≤ -ζ'/ζ(σ)`, obtained by replacing every cosine by `±1`.  On the **upper** side
that is sharp, attained at `t = 0`.  On the **lower** side it is not: by the decoupling of the prime
symbol across primes, the infimum is computed prime by prime, and the local factor
`L(x,cos θ) = Σ_{k≥1} x^k cos kθ` has sharp attained range `[-x/(1+x), x/(1-x)]`.  With
`x = p^{-σ}` these endpoints are `-1/(p^σ+1)` and `1/(p^σ-1)`, and the elementary identity

```text
1/(x+1) = 1/(x-1) - 2/(x²-1)
```

turns the sum of the lower endpoints into a closed form:

```text
Σ_p (log p)/(p^σ + 1) = Σ_p (log p)/(p^σ - 1) - 2 Σ_p (log p)/(p^{2σ} - 1)
                      = -ζ'/ζ(σ) + 2 ζ'/ζ(2σ).
```

Hence, for every real `t` and every `σ > 1`,

```text
Re( -ζ'/ζ(σ + it) )  ≥  ζ'/ζ(σ) - 2 ζ'/ζ(2σ),
```

sharp, with equality approached along the Kronecker orbit.  The correction `-2ζ'/ζ(2σ)` is exactly
what the naive `cos ≥ -1` bound throws away.  The corresponding statement for `|ζ|` itself —
`ζ(2σ)/ζ(σ) ≤ |ζ(σ+it)| ≤ ζ(σ)` — is classical (Titchmarsh); this is its logarithmic-derivative
counterpart, with the sharp constant supplied by the decoupling.

This file formalizes the per-prime content: the algebraic identity, the translation of the local
range into the variables `p^σ`, and the resulting sharp local lower bound with its correction term.
-/

open Real

noncomputable section

namespace RHTower

/-- The elementary identity behind the correction term. -/
theorem one_div_add_one_eq {x : ℝ} (hx : 1 < x) :
    1 / (x + 1) = 1 / (x - 1) - 2 / (x ^ 2 - 1) := by
  have h1 : x - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have h2 : x + 1 ≠ 0 := by intro h; linarith
  have h3 : x ^ 2 - 1 ≠ 0 := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  field_simp
  ring

/-- Translation of the upper endpoint of the local range into the variable `q = p^σ`. -/
theorem localUpper_eq {q : ℝ} (hq : 1 < q) :
    (1 / q) / (1 - 1 / q) = 1 / (q - 1) := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; linarith
  have h1 : q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  field_simp

/-- Translation of the lower endpoint of the local range into the variable `q = p^σ`. -/
theorem localLower_eq {q : ℝ} (hq : 1 < q) :
    (1 / q) / (1 + 1 / q) = 1 / (q + 1) := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; linarith
  have h2 : q + 1 ≠ 0 := by intro h; linarith
  field_simp

/-- **Sharp local lower bound.**  The contribution of a single prime to the real part of the prime
symbol is at least `-log q/(q+1)`, and the identity above rewrites this as the naive bound
`-log q/(q-1)` improved by exactly `2 log q/(q²-1)`. -/
theorem localSymbol_lower {q c lg : ℝ} (hq : 1 < q) (hc : |c| ≤ 1) (hlg : 0 ≤ lg) :
    -(lg / (q - 1)) + 2 * lg / (q ^ 2 - 1) ≤ lg * primeLocalSymbol (1 / q) c := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hx : 0 < 1 / q := by positivity
  have hx1 : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq
  have hL := primeLocalSymbol_ge hx hx1 hc
  rw [localLower_eq hq] at hL
  have hstep : lg * (-(1 / (q + 1))) ≤ lg * primeLocalSymbol (1 / q) c :=
    mul_le_mul_of_nonneg_left hL hlg
  have hid := one_div_add_one_eq hq
  have hrw : lg * (-(1 / (q + 1))) = -(lg / (q - 1)) + 2 * lg / (q ^ 2 - 1) := by
    rw [hid]
    field_simp
    ring
  linarith [hrw ▸ hstep]

/-- **Sharp local upper bound**, for completeness: the naive bound is already attained here, at
`θ = 0`. -/
theorem localSymbol_upper {q c lg : ℝ} (hq : 1 < q) (hc : |c| ≤ 1) (hlg : 0 ≤ lg) :
    lg * primeLocalSymbol (1 / q) c ≤ lg / (q - 1) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hx : 0 < 1 / q := by positivity
  have hx1 : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq
  have hL := primeLocalSymbol_le hx hx1 hc
  rw [localUpper_eq hq] at hL
  have hstep : lg * primeLocalSymbol (1 / q) c ≤ lg * (1 / (q - 1)) :=
    mul_le_mul_of_nonneg_left hL hlg
  calc lg * primeLocalSymbol (1 / q) c ≤ lg * (1 / (q - 1)) := hstep
    _ = lg / (q - 1) := by ring

/-- The correction term is strictly positive, so the sharp lower bound strictly improves the naive
one at every prime. -/
theorem correction_pos {q lg : ℝ} (hq : 1 < q) (hlg : 0 < lg) : 0 < 2 * lg / (q ^ 2 - 1) := by
  have h : (0 : ℝ) < q ^ 2 - 1 := by nlinarith
  positivity

end RHTower
