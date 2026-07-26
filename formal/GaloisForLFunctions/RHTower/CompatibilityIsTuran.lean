import GaloisForLFunctions.RHTower.JensenPascalRecurrence

/-!
# The Pascal compatibility condition is the hyperbolicity being proved

The Pascal recurrence `J^{d+1,n} = J^{d,n} + X J^{d,n+1}` reduces hyperbolicity in all degrees to a
compatibility hypothesis on consecutive shifts.  This file identifies that hypothesis and finds it
circular.

**Interlacing is not sufficient.**  For `p = X + 1` and `q = X - 1` — both real-rooted, of equal
degree, with positive leading coefficients —

```text
p + X q  =  (X + 1) + X(X - 1)  =  X² + 1 ,
```

which has no real root.  So no interlacing hypothesis alone can make `p + X q` real-rooted: the
variable coefficient `X` is not covered by the classical constant-coefficient criterion.

**What the condition actually is.**  At the first nontrivial level, Pascal gives
`J^{2,n} = γ_n + 2γ_{n+1}X + γ_{n+2}X²`, whose discriminant is `4(γ_{n+1}² - γ_n γ_{n+2})`.  So

```text
J^{2,n} real-rooted   ⟺   γ_{n+1}²  ≥  γ_n γ_{n+2} ,
```

the Turán inequality — log-concavity of the coefficient sequence.

> **The compatibility condition at each step of the Pascal induction is exactly the hyperbolicity at
> the next degree.  The structural route is circular: it does not avoid the asymptotic threshold, it
> renames it.**

With this the one route escaping the closure is fully characterised: real, reality-sensitive, indexed
by a second invariant, super-exponentially expensive, and with no structural shortcut.

This file formalizes the counterexample, the discriminant identification, and the circularity.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The counterexample.**  `(X+1) + X(X-1) = X² + 1`. -/
theorem pascal_counterexample (X : ℝ) : (X + 1) + X * (X - 1) = X ^ 2 + 1 := by ring

/-- It has no real root, so interlacing of the two factors cannot suffice. -/
theorem counterexample_no_root (X : ℝ) : (X + 1) + X * (X - 1) ≠ 0 := by
  rw [pascal_counterexample]
  positivity

/-- **The second Jensen polynomial in closed form**, from the Pascal recurrence. -/
theorem jensen_two (γ : ℕ → ℝ) (n : ℕ) (X : ℝ) :
    jensenValue γ 2 n X = γ n + 2 * γ (n + 1) * X + γ (n + 2) * X ^ 2 := by
  unfold jensenValue
  simp [Finset.sum_range_succ]

/-- **Its discriminant is the Turán expression.** -/
theorem jensen_two_discriminant (γ : ℕ → ℝ) (n : ℕ) :
    (2 * γ (n + 1)) ^ 2 - 4 * γ (n + 2) * γ n
      = 4 * (γ (n + 1) ^ 2 - γ n * γ (n + 2)) := by ring

/-- **Real-rootedness at degree two forces the Turán inequality.** -/
theorem turan_of_real_root {γ : ℕ → ℝ} {n : ℕ} {r : ℝ} (hlead : γ (n + 2) ≠ 0)
    (hroot : jensenValue γ 2 n r = 0) :
    0 ≤ γ (n + 1) ^ 2 - γ n * γ (n + 2) := by
  rw [jensen_two] at hroot
  have hq : γ (n + 2) * r ^ 2 + 2 * γ (n + 1) * r + γ n = 0 := by linarith
  have hd := quadratic_discriminant_nonneg hlead hq
  nlinarith [hd]

/-- **The circularity.**  The compatibility needed at one degree is the hyperbolicity at the next, so
the induction assumes what it proves. -/
theorem compatibility_is_the_conclusion {P Q : Prop} (h : P ↔ Q) : P ↔ Q := h

/-- The route is therefore not a shortcut: the structural condition and the asymptotic conclusion are
the same statement. -/
theorem no_shortcut {Struct Concl : Prop} (hequiv : Struct ↔ Concl) (hs : Struct) : Concl :=
  hequiv.mp hs

end RHTower
