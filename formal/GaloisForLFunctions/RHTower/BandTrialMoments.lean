import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Even moments of the band trial weights

The weights `(1 - x²)^k` on `[-1, 1]` are the coefficients of the Kaiser–Bessel trial function of the
band concentration problem, and its finite-Fourier transform is assembled from the moments

```text
M(j, k) = ∫_(-1)^1 x^(2j) (1 - x²)^k dx.
```

These moments have the closed form

```text
M(j, k) · j! · (2j + 2k + 2)! = (2j)! · k! · 4^(k+1) · (j + k + 1)!,
```

proved here with no Beta or Gamma function: the identity `(1-x²)^(k+1) = (1-x²)^k - x²(1-x²)^k` gives
the recursion `M(j, k+1) = M(j, k) - M(j+1, k)`, the base case is an elementary power integral, and the
induction step is the polynomial identity

```text
(2j+2k+4)(2j+2k+3) - 2(2j+1)(j+k+2) = 4(k+1)(j+k+2).
```

The multiplicative form of the statement keeps every step inside the factorials, so no division has to
be cleared.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-- The even moment of the `k`-th trial weight on the band. -/
def trialMoment (j k : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, x ^ (2 * j) * (1 - x ^ 2) ^ k

theorem continuous_trialIntegrand (j k : ℕ) :
    Continuous fun x : ℝ => x ^ (2 * j) * (1 - x ^ 2) ^ k := by
  fun_prop

theorem intervalIntegrable_trialIntegrand (j k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * j) * (1 - x ^ 2) ^ k) volume (-1) 1 :=
  (continuous_trialIntegrand j k).intervalIntegrable _ _

/-- The moments of the trivial weight. -/
theorem trialMoment_zero (j : ℕ) : trialMoment j 0 = 2 / (2 * (j : ℝ) + 1) := by
  have h : trialMoment j 0 = ∫ x in (-1 : ℝ)..1, x ^ (2 * j) := by
    rw [trialMoment]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [pow_zero, mul_one]
  rw [h, integral_pow]
  have hodd : ((-1 : ℝ)) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    simp
  rw [hodd, one_pow]
  push_cast
  ring

/-- **The recursion in the weight exponent.**  It comes from `(1-x²)^(k+1) = (1-x²)^k - x²(1-x²)^k`. -/
theorem trialMoment_succ (j k : ℕ) :
    trialMoment j (k + 1) = trialMoment j k - trialMoment (j + 1) k := by
  have hpt : ∀ x : ℝ, x ^ (2 * j) * (1 - x ^ 2) ^ (k + 1)
      = x ^ (2 * j) * (1 - x ^ 2) ^ k - x ^ (2 * (j + 1)) * (1 - x ^ 2) ^ k := by
    intro x
    have hj : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [hj, pow_succ, pow_add]
    ring
  rw [trialMoment, trialMoment, trialMoment]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_trialIntegrand j k)
    (intervalIntegrable_trialIntegrand (j + 1) k)]
  exact intervalIntegral.integral_congr fun x _ => hpt x

/-- **The closed form of the trial moments**, in multiplicative shape. -/
theorem trialMoment_mul_factorial (k : ℕ) : ∀ j : ℕ,
    trialMoment j k * ((Nat.factorial j : ℝ) * (Nat.factorial (2 * j + 2 * k + 2) : ℝ))
      = (Nat.factorial (2 * j) : ℝ) * (Nat.factorial k : ℝ) * 4 ^ (k + 1)
        * (Nat.factorial (j + k + 1) : ℝ) := by
  induction k with
  | zero =>
    intro j
    rw [trialMoment_zero]
    have h1 : 2 * j + 2 * 0 + 2 = 2 * j + 2 := by ring
    have h2 : j + 0 + 1 = j + 1 := by ring
    rw [h1, h2]
    have hfac : Nat.factorial (2 * j + 2) = (2 * j + 2) * ((2 * j + 1) * Nat.factorial (2 * j)) := by
      rw [Nat.factorial_succ (2 * j + 1)]
      have : 2 * j + 1 + 1 = 2 * j + 2 := by ring
      rw [this, Nat.factorial_succ (2 * j)]
    have hfacj : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    rw [hfac, hfacj]
    have hpos : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ k ih =>
    intro j
    have hrec := trialMoment_succ j k
    have hj := ih j
    have hj1 := ih (j + 1)
    -- expand the two factorials that grow
    have hfac1 : Nat.factorial (2 * j + 2 * (k + 1) + 2)
        = (2 * j + 2 * k + 4) * ((2 * j + 2 * k + 3) * Nat.factorial (2 * j + 2 * k + 2)) := by
      have e1 : 2 * j + 2 * (k + 1) + 2 = (2 * j + 2 * k + 3) + 1 := by ring
      have e2 : 2 * j + 2 * k + 3 = (2 * j + 2 * k + 2) + 1 := by ring
      rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    have hfac2 : Nat.factorial (2 * (j + 1) + 2 * k + 2)
        = Nat.factorial (2 * j + 2 * k + 4) := by
      congr 1
      ring
    have hfac3 : Nat.factorial (2 * j + 2 * k + 4)
        = (2 * j + 2 * k + 4) * ((2 * j + 2 * k + 3) * Nat.factorial (2 * j + 2 * k + 2)) := hfac1
    have hfacj : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    have hfac2j : Nat.factorial (2 * (j + 1)) = (2 * j + 2) * ((2 * j + 1) * Nat.factorial (2 * j)) := by
      have e1 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ, Nat.factorial_succ]
    have hfack : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
    have hfacjk : Nat.factorial (j + (k + 1) + 1) = (j + k + 2) * Nat.factorial (j + k + 1) := by
      have e1 : j + (k + 1) + 1 = (j + k + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ]
    have hfacjk1 : Nat.factorial ((j + 1) + k + 1) = Nat.factorial (j + k + 2) := by
      congr 1
      ring
    have hfacjk2 : Nat.factorial (j + k + 2) = (j + k + 2) * Nat.factorial (j + k + 1) := by
      have e1 : j + k + 2 = (j + k + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ]
    -- the positive factorial values
    have hjpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have hfpos : (0 : ℝ) < (Nat.factorial (2 * j + 2 * k + 2) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hrec]
    rw [hfac1, hfacjk, hfack]
    rw [hfac2, hfac3, hfacj, hfac2j, hfacjk1, hfacjk2] at hj1
    push_cast at hj hj1 ⊢
    have hjne : (Nat.factorial j : ℝ) ≠ 0 := ne_of_gt hjpos
    have hfne : (Nat.factorial (2 * j + 2 * k + 2) : ℝ) ≠ 0 := ne_of_gt hfpos
    field_simp at hj hj1 ⊢
    linear_combination ((2 * (j : ℝ) + 2 * (k : ℝ) + 4) * (2 * (j : ℝ) + 2 * (k : ℝ) + 3)) * hj - hj1

end GaloisForLFunctions.RHTower

end
