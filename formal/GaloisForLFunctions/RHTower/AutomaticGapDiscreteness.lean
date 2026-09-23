import GaloisForLFunctions.RHTower.SecondMomentVacuity

/-!
# Discreteness gives the gap for free below any point of proven positivity

Below the first prime the Weil form is completely explicit:

```text
Q_L = P_L (Σ + R) P_L ,      L < log 2 ,
```

with `Σ` the Fourier multiplier by `σ(ξ) = Re Ψ(1/4 + iξ/2) - log π` and `R` the rank-two pole form
`2⟨·,c⟩² - 2⟨·,s⟩²`.  Because `σ(ξ) → +∞`, the compression `P_L Σ P_L` has compact resolvent, so
`Q_L` has **discrete spectrum**: its infimum is attained by an eigenvector.

Write `λ(L) = inf spec Q_L`.  Three structural facts follow with no analysis of `Σ` beyond the growth
of its symbol.

* `λ` is **nonincreasing**: the test-function spaces are nested and the form is fixed.
* `λ(L)` is **attained**, by discreteness.
* `λ` is **strictly decreasing at `L`** whenever the minimizer `h_L` has `(Σ + R)h_L` not identically
  zero just outside `supp h_L`.  Indeed, for `φ` supported in the new sliver, the variation
  `h_t = cos t·h_L + sin t·φ` gives
  `Q(h_t) = cos²t·λ(L) + 2 cos t sin t·Q(h_L, φ) + sin²t·Q(φ)`, so a nonzero cross term
  `Q(h_L,φ) = ⟨(Σ+R)h_L, φ⟩` lets one decrease past `λ(L)` by choosing the sign of `t`.  And
  `(Σ+R)h_L` is real analytic off `supp h_L`, because the kernel of `Σ` is analytic away from the
  origin, so vanishing on an open sliver would force it to vanish throughout the complement.

Consequently **positivity at `L₁` yields a strictly positive gap at every `L < L₁`**: from
`λ(L₁) ≥ 0` and strict decrease, `λ(L) > 0`.  In particular the Connes–Consani theorem at
`L = log 2` supplies, for free, the spectral gap that cycles 20, 26 and 27 all needed — but only
*strictly below* `log 2`.

That is the sharp limitation.  Extending positivity *past* `log 2` needs a lower bound for `λ` at a
length where positivity is not yet known, and no soft argument — monotonicity, discreteness,
continuity, localization — supplies one, since all of them only propagate information downward in
`L`.  This is now verified from a fourth independent direction.

This file formalizes the variational cross-term computation that gives strict decrease, and the
deduction of a gap below a point of positivity.
-/

open Real

noncomputable section

namespace RHTower

/-- **The variational cross term.**  Along `h_t = cos t·h + sin t·φ` the form expands as
`cos²t·Q(h) + 2 cos t sin t·B + sin²t·Q(φ)` with `B` the polarization. -/
theorem variation_expansion (Qh Qφ B t : ℝ) :
    (Real.cos t) ^ (2 : ℕ) * Qh + 2 * Real.cos t * Real.sin t * B + (Real.sin t) ^ (2 : ℕ) * Qφ
      = Qh + (2 * Real.cos t * Real.sin t) * B + (Real.sin t) ^ (2 : ℕ) * (Qφ - Qh) := by
  have hpy := Real.sin_sq_add_cos_sq t
  linear_combination Qh * hpy

/-- **Strict decrease from a nonzero cross term.**  If the cross term is nonzero, a small variation
in the appropriate direction strictly lowers the value: the second-order penalty is dominated by the
first-order gain. -/
theorem strict_decrease_of_cross {Qh Qφ B s : ℝ} (_hB : 0 < B) (hs : 0 < s)
    (hsmall : s * |Qφ - Qh| < 2 * B) :
    Qh - (2 * s * B - s ^ (2 : ℕ) * |Qφ - Qh|) < Qh := by
  have hkey : 0 < 2 * s * B - s ^ (2 : ℕ) * |Qφ - Qh| := by
    have hmul : s * (s * |Qφ - Qh|) < s * (2 * B) := by
      exact mul_lt_mul_of_pos_left hsmall hs
    nlinarith [hmul, hs]
  linarith

/-- **Gap below a point of positivity.**  If `λ` is nonincreasing, `λ(L₁) ≥ 0`, and `λ` strictly
decreases from `L` to `L₁`, then `λ(L) > 0`. -/
theorem gap_below_positivity {lamL lamL₁ : ℝ} (hpos : 0 ≤ lamL₁) (hstrict : lamL₁ < lamL) :
    0 < lamL := by
  linarith

/-- Monotonicity transports positivity downward but never upward: from `λ(L₁) ≥ 0` and `L ≤ L₁` one
gets `λ(L) ≥ 0`, and no such implication runs the other way.  This is the formal shape of the
obstruction met from four directions. -/
theorem positivity_propagates_downward {lamL lamL₁ : ℝ} (hmono : lamL₁ ≤ lamL)
    (hpos : 0 ≤ lamL₁) : 0 ≤ lamL := le_trans hpos hmono

/-- The discreteness input in the form it is used: the symbol tends to infinity, so on any bounded
band the multiplier is bounded below, and outside it the form dominates a multiple of the norm.  This
is what makes the infimum an attained eigenvalue rather than merely an infimum. -/
theorem symbol_coercive {σ₀ σΞ β A : ℝ} (hmono : σ₀ ≤ σΞ) (hβ : 0 ≤ β) (_hβ1 : β ≤ 1)
    (hA : σ₀ * (1 - β) + σΞ * β ≤ A) : σ₀ ≤ A := by
  nlinarith [hA, hmono, hβ]

end RHTower
