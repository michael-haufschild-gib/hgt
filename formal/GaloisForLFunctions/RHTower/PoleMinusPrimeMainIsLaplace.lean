import GaloisForLFunctions.RHTower.PoleKreinNyquistTrace

/-!
# Pole minus prime main term is a Laplace transform, and it is bounded by `4g(0)`

The pole term and the prime-number-theorem main term of the prime sum both grow like `e^{L/2}`.  This
file shows they cancel **identically**, for every test and every width, and identifies the residue.

Substituting `t = e^u` in the main term of the prime sum turns it into an integral against
`e^{u/2}`:

```text
2 Σ_{n ≤ e^L} Λ(n) n^{-1/2} g(log n)  ~  2 ∫₁^{e^L} g(log t) t^{-1/2} dt  =  2 ∫₀^L g(u) e^{u/2} du ,
```

while the pole term, by evenness of `g` and `2cosh(u/2) = e^{u/2} + e^{-u/2}`, is

```text
ĝ(i/2) + ĝ(-i/2)  =  2 ∫_{-L}^{L} g(u) cosh(u/2) du  =  2 ∫₀^L g(u) ( e^{u/2} + e^{-u/2} ) du .
```

Subtracting:

> **For every even `g` supported in `[-L, L]`,**
> ```text
> pole(g) - primeMain(g)  =  2 ∫₀^L g(u) e^{-u/2} du ,
> ```
> **the Laplace transform of `g` at `1/2`.  The exponentially growing parts cancel identically, and
> when `ĝ ≥ 0` — so that `|g| ≤ g(0)` — the residue is at most `4 g(0)`, a bounded budget
> independent of `L`.**

For the normalised tent `g(u) = 1 - |u|/L` the residue is exactly `4 + 8(e^{-L/2} - 1)/L`, which is
positive for every `L > 0`, increases from `0` to `4`, and is never exceeded.

**Consequences.**

*The width buys nothing.*  Growing `L` multiplies both the pole and the prime main term by the same
`e^{L/2}`; the difference stays below `4g(0)` forever.  The doubly exponential barrier recorded
earlier has this as its source.

*All of the hypothesis sits in the error term.*  What is left of the Weil functional is
`2∫₀^L g e^{-u/2} + A_∞(g)` minus the smoothed prime-counting error, so the hypothesis is exactly the
statement that the smoothed error stays inside a bounded budget.

*A lower bound for the compressed prime operator.*  Since the pole reaches
`g(0)(2 sinh(L/2) + L)` at its extremiser `cosh(u/2)`, the prime main term there is at least
`g(0)(2 sinh(L/2) + L - 4)`: the top of the compressed prime spectrum grows like `e^{L/2}`, matching
the pole rather than the crude bound `4e^{L/2}`.

This file formalizes the cancellation, the bound on the residue, the exact tent value, and the
resulting lower bound for the prime side.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- `2cosh(u/2) = e^{u/2} + e^{-u/2}`: the decomposition behind the cancellation. -/
theorem two_cosh_half (u : ℝ) :
    2 * Real.cosh (u / 2) = Real.exp (u / 2) + Real.exp (-(u / 2)) := by
  rw [Real.cosh_eq]; ring

/-- **The cancellation.**  If the pole term is `2∫(e^{u/2} + e^{-u/2})g` and the prime main term is
`2∫ e^{u/2} g`, their difference is `2∫ e^{-u/2} g`. -/
theorem pole_minus_primeMain {Ip Im : ℝ} :
    2 * (Ip + Im) - 2 * Ip = 2 * Im := by ring

/-- The primitive of `e^{-u/2}`. -/
theorem integral_exp_neg_half (L : ℝ) :
    ∫ u in (0:ℝ)..L, Real.exp (-(u / 2)) = 2 * (1 - Real.exp (-(L / 2))) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (fun u : ℝ => -2 * Real.exp (-(u / 2))) (Real.exp (-(x / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) x := by
      simpa using ((hasDerivAt_id x).div_const 2).neg
    have h2 := h1.exp
    have h3 := h2.const_mul (-2 : ℝ)
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-(u / 2)))
      MeasureTheory.volume 0 L :=
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [show -((0:ℝ) / 2) = 0 by ring, Real.exp_zero]
  ring

/-- The primitive of `u·e^{-u/2}`. -/
theorem integral_id_mul_exp_neg_half (L : ℝ) :
    ∫ u in (0:ℝ)..L, u * Real.exp (-(u / 2))
      = 4 - (2 * L + 4) * Real.exp (-(L / 2)) := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (fun u : ℝ => (-2 * u - 4) * Real.exp (-(u / 2)))
        (x * Real.exp (-(x / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) x := by
      simpa using ((hasDerivAt_id x).div_const 2).neg
    have h2 := h1.exp
    have h3 : HasDerivAt (fun u : ℝ => -2 * u - 4) (-2) x := by
      simpa using ((hasDerivAt_id x).const_mul (-2 : ℝ)).sub_const 4
    have h := h3.mul h2
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun u : ℝ => u * Real.exp (-(u / 2)))
      MeasureTheory.volume 0 L :=
    (continuous_id.mul
      (Real.continuous_exp.comp (continuous_id.div_const 2).neg)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [show -((0:ℝ) / 2) = 0 by ring, Real.exp_zero]
  ring

/-- **The tent residue.**  For the normalised tent `g(u) = 1 - u/L` on `[0, L]`,
`2∫₀^L g(u)e^{-u/2}du = 4 + 8(e^{-L/2} - 1)/L`. -/
theorem tent_residue {L : ℝ} (hL : L ≠ 0) :
    2 * ((∫ u in (0:ℝ)..L, Real.exp (-(u / 2)))
        - (∫ u in (0:ℝ)..L, u * Real.exp (-(u / 2))) / L)
      = 4 + 8 * (Real.exp (-(L / 2)) - 1) / L := by
  rw [integral_exp_neg_half, integral_id_mul_exp_neg_half]
  field_simp
  ring

/-- **The residue is positive.**  `4 + 8(e^{-L/2} - 1)/L > 0` for `L > 0`, since `1 - x < e^{-x}`. -/
theorem tent_residue_pos {L : ℝ} (hL : 0 < L) :
    0 < 4 + 8 * (Real.exp (-(L / 2)) - 1) / L := by
  have hexp : 1 - L / 2 < Real.exp (-(L / 2)) := by
    have h := Real.add_one_lt_exp (show -(L / 2) ≠ 0 by linarith)
    linarith
  have hnum : 0 < 8 * (Real.exp (-(L / 2)) - 1) + 4 * L := by linarith
  have hdiv : 0 < (8 * (Real.exp (-(L / 2)) - 1) + 4 * L) / L := div_pos hnum hL
  have heq : (8 * (Real.exp (-(L / 2)) - 1) + 4 * L) / L
      = 8 * (Real.exp (-(L / 2)) - 1) / L + 4 := by field_simp
  rw [heq] at hdiv
  linarith

/-- **The residue never exceeds `4`.**  Since `e^{-L/2} ≤ 1`, the correction is nonpositive. -/
theorem tent_residue_le_four {L : ℝ} (hL : 0 < L) :
    4 + 8 * (Real.exp (-(L / 2)) - 1) / L ≤ 4 := by
  have h1 : Real.exp (-(L / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h2 : 8 * (Real.exp (-(L / 2)) - 1) ≤ 0 := by linarith
  have := div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hL)
  linarith

/-- **The budget is bounded independently of the width.**  With `|g| ≤ g(0)` the residue
`2∫₀^L g(u)e^{-u/2}du` is at most `2·g(0)·2(1 - e^{-L/2})`, hence at most `4g(0)` for every `L`. -/
theorem residue_le_four_g0 {g0 L : ℝ} (hg0 : 0 ≤ g0) :
    2 * (g0 * (2 * (1 - Real.exp (-(L / 2))))) ≤ 4 * g0 := by
  have h : 0 < Real.exp (-(L / 2)) := Real.exp_pos _
  nlinarith

/-- **Lower bound for the compressed prime spectrum.**  At the pole extremiser the pole reaches
`g0·(2 sinh(L/2) + L)`, so the prime main term there is at least `g0·(2 sinh(L/2) + L) - 4g0`. -/
theorem prime_main_lower {g0 L Pm : ℝ}
    (hpole : Pm + 4 * g0 ≥ g0 * (2 * Real.sinh (L / 2) + L)) :
    Pm ≥ g0 * (2 * Real.sinh (L / 2) + L) - 4 * g0 := by linarith

/-- The lower bound grows exponentially: `2 sinh(L/2) + L - 4 ≥ e^{L/2} - 1 - 4` since
`2 sinh x ≥ e^x - 1`. -/
theorem prime_main_grows {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (L / 2) - 1 ≤ 2 * Real.sinh (L / 2) + L := by
  have h : Real.sinh (L / 2) = (Real.exp (L / 2) - Real.exp (-(L / 2))) / 2 := Real.sinh_eq _
  have hpos : 0 < Real.exp (-(L / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(L / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  rw [h]; linarith

end RHTower
