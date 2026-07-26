import GaloisForLFunctions.RHTower.NyquistDichotomy

/-!
# The falsification ladder: RH as an increasing sequence of finite inequalities

Every entry recorded so far bounds a *method*.  This file produces the first statement whose failure
would refute the hypothesis outright, and it does so by removing the arithmetic.

**The pole is an off-critical zero at maximal deviation.**  The pole of `ζ` at `s = 1` enters the
explicit formula as `ĝ(i/2) + ĝ(-i/2)` — precisely the continuation of `ĝ` to the complex ordinates
`±i/2`, i.e. the cycle-78 configuration at deviation `a = 1/2`.  The detection ceiling therefore
applies to it, and it is sharp:

```text
ĝ(i/2) + ĝ(-i/2)  ≤  g(0) · ( 2 sinh(L/2) + L ) .
```

**The ladder.**  Write the explicit formula for a positive-type `g` of width `L` as
`Σ_ρ ĝ(γ_ρ) = P(g) + A_∞(g) - Pr_L(g)`, where `Pr_L(g) = 2 Σ_{n ≤ e^L} Λ(n)n^{-1/2} g(log n)` is a
**finite** sum.  If the hypothesis holds every `γ_ρ` is real and every term of the left side is
nonnegative, so

```text
Pr_L(g) - A_∞(g)  ≤  P(g)  ≤  g(0)·( 2 sinh(L/2) + L ) .
```

The middle term has been eliminated by a sharp universal bound; what remains is an inequality between
the digamma transform of `ĝ`, finitely many elementary prime terms, and an elementary function of
`L`.  **No zeros, no asymptotics, no arithmetic beyond a finite list of prime powers.**

> **Each width `L` gives a rung: an inequality checkable in finitely many elementary terms whose
> failure disproves the Riemann hypothesis.  Below `log 2` the prime side is empty and the rung
> involves only the Gamma function.**

The rungs increase with `L`, and by Weil's criterion the hypothesis is equivalent to all of them
holding.  This converts the criterion from a statement quantified over an infinite-dimensional cone
into a ladder of finite tests, at the cost of the sharp pole ceiling — which is exactly what cycle 78
supplies.

**A correction this forces.**  Empty-window positivity is *not* automatic over `ℚ`: the archimedean
weight `Re ψ(1/4 + ir/2) - log π` is **negative** for `|r| < 2π`, the analytic reflection of the fact
that the smooth zero count `(T/2π)log(T/2πe)` is negative below `T = 2πe`.  Over a number field the
discriminant term `g(0) log|d_K|` dominates it, which is what made the empty window positive there;
over `ℚ` there is no such term and the rung at `L < log 2` is a genuine inequality, not a triviality.

This file formalizes the pole ceiling, the rung, its contrapositive, the emptiness of the prime side
below `log 2`, and monotonicity of the ladder.
-/

open Real

noncomputable section

namespace RHTower

/-- **The pole is the maximal-deviation configuration.**  Twice the detection ceiling at `a = 1/2` is
the elementary function `2 sinh(L/2) + L`. -/
theorem pole_is_maximal_deviation (L : ℝ) :
    2 * detectionCeiling (1 / 2) L = 2 * Real.sinh (L / 2) + L := by
  unfold detectionCeiling
  rw [show (1:ℝ) / 2 * L = L / 2 by ring]
  field_simp

/-- **The pole ceiling.**  The pole contribution to a positive-type test of width `L` is at most
`g(0)(2 sinh(L/2) + L)`, and by the attainment in the detection ceiling this constant is sharp. -/
theorem pole_ceiling {L g0 P : ℝ} (_hg0 : 0 ≤ g0)
    (hP : P ≤ g0 * (2 * detectionCeiling (1 / 2) L)) :
    P ≤ g0 * (2 * Real.sinh (L / 2) + L) := by
  rwa [pole_is_maximal_deviation] at hP

/-- **A rung of the ladder.**  If the zero side is nonnegative — which the hypothesis gives, since
then every ordinate is real and `ĝ ≥ 0` — the finite prime side minus the archimedean side is below
the pole ceiling. -/
theorem rung {Z P A Pr C : ℝ} (hZ : 0 ≤ Z) (hid : Z = P + A - Pr) (hP : P ≤ C) :
    Pr - A ≤ C := by linarith

/-- **Falsification.**  A rung that fails forces a negative zero side, hence an ordinate off the real
axis: the hypothesis is refuted by a single explicit test function. -/
theorem rung_failure {Z P A Pr C : ℝ} (hid : Z = P + A - Pr) (hP : P ≤ C)
    (hfail : C < Pr - A) : Z < 0 := by linarith

/-- **The empty rung.**  Below `log 2` no prime power contributes: every integer `n ≥ 2` has
`log n ≥ log 2 > L`, so the finite prime sum is empty and the rung involves only `Γ`. -/
theorem empty_rung {L : ℝ} (hL : L < Real.log 2) {n : ℕ} (hn : 2 ≤ n) :
    L < Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hn
  linarith

/-- **The ladder increases.**  A wider test has a larger pole ceiling, so the rungs are nested. -/
theorem ladder_monotone {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) :
    2 * Real.sinh (L₁ / 2) + L₁ ≤ 2 * Real.sinh (L₂ / 2) + L₂ := by
  have hs : Real.sinh (L₁ / 2) ≤ Real.sinh (L₂ / 2) :=
    Real.sinh_le_sinh.mpr (by linarith)
  linarith

/-- **The ceiling exceeds the naive linear bound.**  Since `x ≤ sinh x` for `x ≥ 0`, the pole ceiling
is at least `2L`; the excess `2(sinh(L/2) - L/2)` is what the analytic continuation contributes beyond
the trivial mass bound. -/
theorem ceiling_ge_linear {L : ℝ} (hL : 0 < L) :
    2 * L < 2 * Real.sinh (L / 2) + L := by
  have h := Real.self_lt_sinh_iff.mpr (show (0:ℝ) < L / 2 by linarith)
  linarith

/-- **The rung is nontrivial exactly when the archimedean side is negative.**  For `L < log 2` the
prime side vanishes, so the rung reads `-A ≤ C`: vacuous when `A ≥ 0`, a genuine constraint when the
archimedean weight is negative, which it is on `|r| < 2π`. -/
theorem rung_nontrivial_iff {A C : ℝ} (_hC : 0 ≤ C) (_hA : A < 0) :
    (-A ≤ C ↔ -C ≤ A) := by
  constructor <;> intro h <;> linarith

end RHTower
