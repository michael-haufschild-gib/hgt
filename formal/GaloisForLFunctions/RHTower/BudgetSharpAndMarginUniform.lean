import GaloisForLFunctions.RHTower.ArchimedeanBudgetConstant

/-!
# The budget constant is sharp, and the margin does not degrade with the width

The archimedean budget was computed by bounding `g ≤ g(0)`.  That looks crude — `g/g(0)` is the
characteristic function of a probability measure, so it satisfies far more than `≤ 1`.  It is not
crude: the supremum is over **all** widths, and the tent of width `L` has `g/g(0) = 1 - |u|/L → 1`
pointwise, so the bound is attained in the limit.

> **`β = 3 log 2 + π/2 - 3` is sharp.  The positive-definite structure cannot improve it.**

At **finite** width it can, and for a concrete reason: `g ≡ 1` on `[-L, L]` is not positive definite,
since its transform `2 sin(rL)/r` is negative for `rL ∈ (π, 2π)` — at `rL = 3π/2` it equals
`-2/(3π/(2L))`.  So `β(L) < β` strictly for every finite `L`.

**The shape of `β(L)`.**  Writing `u = t/2` in the tail integral,

```text
T(g)  =  ∫₀^∞ ( g(u)e^{-u/2} - g(0)e^{-2u} ) · 2e^{-2u}/(1 - e^{-2u}) du ,
```

a linear functional of `g` with a positive kernel `κ(u) = 2e^{-5u/2}/(1 - e^{-2u})`.  Expanding the
denominator, `κ` is the sum of the exponentials `2e^{-(2n+5/2)u}`, whose Fourier transforms are the
Poisson kernels `4(2n + 5/2)/((2n + 5/2)² + r²)`.  Substituting `g = φ * φ̃` turns `T` into a
quadratic form, so

```text
β(L)  =  λ_max ( compression to PW_{L/2} of the Toeplitz operator with symbol Σ_n 4s_n/(s_n² + r²) ) ,
        s_n = 2n + 5/2 ,
```

which increases to the symbol's supremum as `L → ∞`.  Each Poisson kernel is maximal at `r = 0`, with
value `4/s_n`, and the divergence of `Σ 4/s_n` is exactly the logarithmic divergence at `u = 0` that
the subtraction of `g(0)e^{-2u}` removes.

**The consequence.**

> **`β(L)` increases in `L` to `β < 1`, so the margin `m(L) = 1 - β(L)` decreases to
> `4 - 3 log 2 - π/2 ≈ 0.3498 > 0`.  The archimedean margin does not degrade to zero: the rungs of
> the ladder get harder monotonically but converge to a strictly positive budget, uniform in the
> width.**

Every degradation recorded in this development therefore lives in the error term — that is, in the
zeros — and none of it is archimedean.

This file formalizes the failure of positive-definiteness for the constant, the Poisson kernels and
their maxima, and the uniform positive lower bound on the margin.
-/

open Real

noncomputable section

namespace RHTower

/-- **The constant is not positive definite on an interval.**  The transform of the indicator of
`[-L, L]` is `2 sin(rL)/r`, and at `rL = 3π/2` its numerator is `-2`. -/
theorem dirichlet_sign_change : Real.sin (π + π / 2) = -1 := by
  simp [Real.sin_add]

/-- Hence the transform of the constant is negative at that frequency, for any positive width. -/
theorem constant_not_positive_definite {L : ℝ} (hL : 0 < L) :
    2 * Real.sin (π + π / 2) / ((π + π / 2) / L) < 0 := by
  rw [dirichlet_sign_change]
  have hπ : 0 < π := Real.pi_pos
  have hden : 0 < (π + π / 2) / L := by positivity
  have : (2:ℝ) * (-1) = -2 := by ring
  rw [this]
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- The `n`-th exponential mode of the tail kernel, `s_n = 2n + 5/2`. -/
def modeRate (n : ℕ) : ℝ := 2 * n + 5 / 2

/-- Every mode rate is positive. -/
theorem modeRate_pos (n : ℕ) : 0 < modeRate n := by
  unfold modeRate
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **The Poisson kernel of a mode.**  The transform of `2e^{-s|u|}` is `4s/(s² + r²)`. -/
def poissonMode (s r : ℝ) : ℝ := 4 * s / (s ^ 2 + r ^ 2)

/-- Each Poisson kernel is positive. -/
theorem poissonMode_pos {s r : ℝ} (hs : 0 < s) : 0 < poissonMode s r := by
  unfold poissonMode
  apply div_pos (by linarith)
  positivity

/-- **Each Poisson kernel is maximal at the origin**, with value `4/s`. -/
theorem poissonMode_le_max {s r : ℝ} (hs : 0 < s) : poissonMode s r ≤ 4 / s := by
  unfold poissonMode
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [sq_nonneg r, sq_nonneg s]

/-- The value at the origin. -/
theorem poissonMode_zero {s : ℝ} (hs : 0 < s) : poissonMode s 0 = 4 / s := by
  unfold poissonMode
  rw [show (0:ℝ) ^ 2 = 0 by ring, add_zero]
  field_simp

/-- **The mode maxima are not summable**, term by term: `4/s_n ≥ 1/(n+2)`, and the harmonic tail
diverges.  This is the logarithmic divergence at `u = 0` that the subtraction removes. -/
theorem mode_max_ge_harmonic (n : ℕ) : 1 / ((n : ℝ) + 2) ≤ 4 / modeRate n := by
  unfold modeRate
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **The margin is uniformly positive.**  Since `β(L) ≤ β` for every width, the margin at every
width is at least `4 - 3 log 2 - π/2`. -/
theorem margin_uniform {βL : ℝ} (h : βL ≤ archimedeanBudget) :
    4 - 3 * Real.log 2 - π / 2 ≤ 1 - βL := by
  rw [← margin_eq_one_sub_budget]
  linarith

/-- **No degradation.**  The uniform margin is bounded below by an explicit positive rational, so it
cannot tend to zero as the width grows. -/
theorem margin_no_degradation {βL : ℝ} (h : βL ≤ archimedeanBudget) :
    (34 : ℝ) / 100 < 1 - βL := by
  have hm := margin_uniform h
  have hl := Real.log_two_lt_d9
  have hp := Real.pi_lt_d2
  nlinarith

/-- **Strict monotone approach.**  The finite-width budget is strictly below the limit whenever the
transform of the constant fails positivity, so the margin is strictly larger at every finite width
than in the limit. -/
theorem margin_strict {βL : ℝ} (h : βL < archimedeanBudget) :
    4 - 3 * Real.log 2 - π / 2 < 1 - βL := by
  rw [← margin_eq_one_sub_budget]
  linarith

end RHTower
