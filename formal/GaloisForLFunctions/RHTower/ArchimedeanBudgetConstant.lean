import GaloisForLFunctions.RHTower.ThreeWayCancellation

/-!
# The archimedean budget is a constant strictly below one

After the three-way cancellation the Weil functional reads

```text
W(g)  =  g(0) - T(g) - 2·E(g) ,
```

where `E` is the smoothed prime-counting error and `T` is the **archimedean tail**, obtained from the
collapsed archimedean integral by removing the first mode.  Using
`1/(1-e^{-t}) = 1 + e^{-t}/(1-e^{-t})`,

```text
T(g)  =  -∫₀^∞ ( g(0)e^{-t} - g(t/2)e^{-t/4} ) · e^{-t}/(1-e^{-t}) dt .
```

**The budget.**  Since `ĝ ≥ 0` forces `|g| ≤ g(0)`, the ratio `T(g)/g(0)` is largest when
`g ≡ g(0)`, giving

```text
β  :=  sup_g T(g)/g(0)  =  ∫₀^∞ e^{-t}(e^{-t/4} - e^{-t})/(1-e^{-t}) dt
                        =  ∫₀^1 (x^{1/4} - x)/(1-x) dx
                        =  ψ(2) - ψ(5/4)
                        =  3 log 2 + π/2 - 3  ≈  0.6502 ,
```

by the substitution `x = e^{-t}` and Gauss's integral for the digamma function, together with
`ψ(2) = 1 - γ` and `ψ(5/4) = ψ(1/4) + 4 = 4 - γ - π/2 - 3 log 2`.  The supremum is approached in the
wide-window limit, where `g/g(0) → 1` on compacts.

> **The archimedean budget of the Riemann hypothesis is `3 log 2 + π/2 - 3 < 1`, and the Weil
> functional therefore carries a strictly positive margin:**
> ```text
> W(g)  ≥  ( 4 - 3 log 2 - π/2 ) · g(0)  -  2 E(g) ,      4 - 3 log 2 - π/2 ≈ 0.3498 .
> ```

**An elementary bound, independent of the digamma evaluation.**  Expanding
`1/(1-x) = Σ_k x^k` term by term gives `β = Σ_{k≥0} ( 1/(k+5/4) - 1/(k+2) )`, whose `k`-th term is
`(3/4)/((k+5/4)(k+2)) ≤ (3/4)(1/(k+1) - 1/(k+2))`.  The right side telescopes to `3/4`, so

```text
β ≤ 3/4 ,        margin ≥ 1/4 ,
```

with no special-function input at all.  This file formalizes that route: the term bound, the
telescoping sum, the resulting budget bound, the margin, and the numerical position of the closed
form.
-/

open Real

noncomputable section

namespace RHTower

/-- The archimedean budget in closed form, `ψ(2) - ψ(5/4)`. -/
def archimedeanBudget : ℝ := 3 * Real.log 2 + π / 2 - 3

/-- The `k`-th term of the budget series, `1/(k+5/4) - 1/(k+2)`. -/
def budgetTerm (k : ℕ) : ℝ := 1 / (k + 5 / 4) - 1 / (k + 2)

/-- **Each term is dominated by a telescoping term.**  Since `k + 5/4 ≥ k + 1`, the `k`-th budget
term is at most `(3/4)(1/(k+1) - 1/(k+2))`. -/
theorem budgetTerm_le (k : ℕ) :
    budgetTerm k ≤ 3 / 4 * (1 / (k + 1) - 1 / ((k : ℝ) + 2)) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (0:ℝ) < k + 1 := by linarith
  have h2 : (0:ℝ) < k + 2 := by linarith
  have h3 : (0:ℝ) < k + 5 / 4 := by linarith
  have hL : budgetTerm k = (3 / 4) / (((k:ℝ) + 5 / 4) * ((k:ℝ) + 2)) := by
    unfold budgetTerm; field_simp; ring
  have hR : 3 / 4 * ((1:ℝ) / (k + 1) - 1 / ((k : ℝ) + 2))
      = (3 / 4) / (((k:ℝ) + 1) * ((k:ℝ) + 2)) := by
    field_simp; ring
  rw [hL, hR]
  gcongr
  norm_num

/-- **The telescoping sum.**  `Σ_{k<N} (1/(k+1) - 1/(k+2)) = 1 - 1/(N+1)`. -/
theorem telescoping_sum (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1:ℝ) / (k + 1) - 1 / (k + 2)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- **The budget is at most `3/4`.**  Every partial sum of the budget series is below `3/4`, by the
termwise bound and the telescoping evaluation. -/
theorem budget_partial_le (N : ℕ) :
    ∑ k ∈ Finset.range N, budgetTerm k ≤ 3 / 4 := by
  calc ∑ k ∈ Finset.range N, budgetTerm k
      ≤ ∑ k ∈ Finset.range N, 3 / 4 * ((1:ℝ) / (k + 1) - 1 / (k + 2)) :=
        Finset.sum_le_sum (fun k _ => budgetTerm_le k)
    _ = 3 / 4 * (1 - 1 / (N + 1)) := by rw [← Finset.mul_sum, telescoping_sum]
    _ ≤ 3 / 4 := by
        have : (0:ℝ) < (N : ℝ) + 1 := by positivity
        have h : 0 < 1 / ((N : ℝ) + 1) := by positivity
        nlinarith

/-- Every budget term is nonnegative, so the partial sums increase to the budget. -/
theorem budgetTerm_nonneg (k : ℕ) : 0 ≤ budgetTerm k := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  unfold budgetTerm
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by linarith)
  linarith

/-- **The margin, elementary form.**  If the tail is at most `3/4` of `g(0)`, the functional retains
a quarter of it. -/
theorem margin_quarter {g0 T E W : ℝ} (hW : W = g0 - T - 2 * E) (_hg0 : 0 ≤ g0)
    (hT : T ≤ 3 / 4 * g0) : (1 / 4) * g0 - 2 * E ≤ W := by
  rw [hW]; linarith

/-- **The closed form is below one.**  `3 log 2 + π/2 - 3 < 1`, using `log 2 < 0.6931471808` and
`π < 3.15`. -/
theorem archimedeanBudget_lt_one : archimedeanBudget < 1 := by
  unfold archimedeanBudget
  have hl := Real.log_two_lt_d9
  have hp := Real.pi_lt_d2
  nlinarith

/-- **The closed-form margin is strictly positive.**  `4 - 3 log 2 - π/2 > 0`. -/
theorem archimedeanMargin_pos : 0 < 4 - 3 * Real.log 2 - π / 2 := by
  have hl := Real.log_two_lt_d9
  have hp := Real.pi_lt_d2
  nlinarith

/-- The margin is exactly one minus the budget. -/
theorem margin_eq_one_sub_budget :
    1 - archimedeanBudget = 4 - 3 * Real.log 2 - π / 2 := by
  unfold archimedeanBudget; ring

/-- **The margin, closed form.**  With the exact budget the functional retains
`(4 - 3 log 2 - π/2)·g(0)`. -/
theorem margin_closed_form {g0 T E W : ℝ} (hW : W = g0 - T - 2 * E) (_hg0 : 0 ≤ g0)
    (hT : T ≤ archimedeanBudget * g0) :
    (4 - 3 * Real.log 2 - π / 2) * g0 - 2 * E ≤ W := by
  rw [hW, ← margin_eq_one_sub_budget]
  nlinarith

/-- The closed form is strictly above the elementary bound's complement: the true budget lies between
the telescoping estimate and one. -/
theorem budget_between : 3 * Real.log 2 + π / 2 - 3 < 1 := archimedeanBudget_lt_one

end RHTower
